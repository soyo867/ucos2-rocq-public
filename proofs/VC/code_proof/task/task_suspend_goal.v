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
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskSuspend -----*)

Definition OSTaskSuspend_safety_wit_1 := 
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (prio_pre = request)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition OSTaskSuspend_safety_wit_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (retval: Z) (PreH1 : (task_suspend_entry_facts sg request )) (PreH2 : (task_suspend_completed_calls critical sg caller request mask before )) (PreH3 : (task_suspend_scheduler_clients critical caller )) (PreH4 : (task_suspend_entry_facts sg request )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_save_history_post environment critical saved_local sg caller mask retval before )
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskSuspend_safety_wit_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (0 <= prio)) (PreH3 : (prio <= 63)) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH7 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition OSTaskSuspend_safety_wit_4 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 71 0 acquired )) (PreH3 : (prio = 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> 63)
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskSuspend_safety_wit_5 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (prio <> 63)) (PreH6 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH12 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskSuspend_safety_wit_6 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 72 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> (task_suspend_resolved_priority (sg) (request) (priority)))
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskSuspend_safety_wit_7 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (prio <> 63)) (PreH7 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskSuspend_safety_wit_8 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 67 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (prio <> 63)) (PreH9 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH15 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> 1)
  **  ((( &( "prio" ) )) # UChar  |-> (task_suspend_resolved_priority (sg) (request) (priority)))
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskSuspend_safety_wit_9 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH6 : ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) ))) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr (task_suspend_state (acquired) (tid) (target)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskSuspend_entail_wit_1_1 := 
(
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) = 255)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> request)
  **  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
) \/
(
forall (prio_pre: Z) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) = 255)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  TT && emp 
|--
  “ (task_suspend_entry_facts sg prio_pre ) ”
  &&  emp
).

Definition OSTaskSuspend_entail_wit_1_1_split_goal_1 := 
forall (prio_pre: Z) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) = 255)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_entry_facts sg prio_pre )
.

Definition OSTaskSuspend_entail_wit_1_2 := 
(
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (prio_pre <> 63)) (PreH3 : (prio_pre = request)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> request)
  **  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
) \/
(
forall (prio_pre: Z) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (prio_pre <> 63)) (PreH3 : (prio_pre = request)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  TT && emp 
|--
  “ (task_suspend_entry_facts sg prio_pre ) ”
  &&  emp
).

Definition OSTaskSuspend_entail_wit_1_2_split_goal_1 := 
forall (prio_pre: Z) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (prio_pre <> 63)) (PreH3 : (prio_pre = request)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_entry_facts sg prio_pre )
.

Definition OSTaskSuspend_entail_wit_2 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (retval: Z) (PreH1 : (task_suspend_entry_facts sg request )) (PreH2 : (task_suspend_completed_calls critical sg caller request mask before )) (PreH3 : (task_suspend_scheduler_clients critical caller )) (PreH4 : (task_suspend_entry_facts sg request )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_save_history_post environment critical saved_local sg caller mask retval before )
  **  (frame )
|--
  EX (acquired_call: TaskSuspendCaller)  (acquired: UCOS2_Verify_State)  (pointer: Z)  (priority: Z)  (residual: Assertion) ,
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before retval acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask retval before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call retval acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (retval: Z) (PreH1 : (task_suspend_entry_facts sg request )) (PreH2 : (task_suspend_completed_calls critical sg caller request mask before )) (PreH3 : (task_suspend_scheduler_clients critical caller )) (PreH4 : (task_suspend_entry_facts sg request )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_save_history_post environment critical saved_local sg caller mask retval before )
  **  (frame )
|--
  EX (acquired_call: TaskSuspendCaller)  (acquired: UCOS2_Verify_State)  (pointer: Z)  (priority: Z)  (residual: Assertion) ,
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before retval acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask retval before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call retval acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
).

Definition OSTaskSuspend_entail_wit_3_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH7 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
|--
  “ (priority = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH7 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  TT && emp 
|--
  “ (priority <= 63) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority = (task_suspend_resolved_priority (sg) (request) (priority))) ”
  &&  emp
).

Definition OSTaskSuspend_entail_wit_3_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH7 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (priority <= 63)
.

Definition OSTaskSuspend_entail_wit_3_1_split_goal_2 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH7 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (0 <= priority)
.

Definition OSTaskSuspend_entail_wit_3_1_split_goal_3 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH7 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (priority = (task_suspend_resolved_priority (sg) (request) (priority)))
.

Definition OSTaskSuspend_entail_wit_3_2 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request = priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
|--
  “ (request = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request = priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  TT && emp 
|--
  “ (request <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request = (task_suspend_resolved_priority (sg) (request) (request))) ”
  &&  emp
).

Definition OSTaskSuspend_entail_wit_3_2_split_goal_1 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request = priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (request <= 63)
.

Definition OSTaskSuspend_entail_wit_3_2_split_goal_2 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request = priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (0 <= request)
.

Definition OSTaskSuspend_entail_wit_3_2_split_goal_3 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request = priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (request = (task_suspend_resolved_priority (sg) (request) (request)))
.

Definition OSTaskSuspend_entail_wit_3_3 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request <> priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
|--
  “ (request = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request <> priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  TT && emp 
|--
  “ (request <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request = (task_suspend_resolved_priority (sg) (request) (priority))) ”
  &&  emp
).

Definition OSTaskSuspend_entail_wit_3_3_split_goal_1 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request <> priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (request <= 63)
.

Definition OSTaskSuspend_entail_wit_3_3_split_goal_2 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request <> priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (0 <= request)
.

Definition OSTaskSuspend_entail_wit_3_3_split_goal_3 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (request <> priority)) (PreH4 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (request = (task_suspend_resolved_priority (sg) (request) (priority)))
.

Definition OSTaskSuspend_entail_wit_4_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH6 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH11 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH12 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (task_suspend_target_facts sg acquired prio tid target )) (PreH15 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH16 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH20 : (task_suspend_target_facts sg acquired prio tid target )) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH22 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (prio <> 63)) (PreH27 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH28 : (0 <= prio)) (PreH29 : (prio <= 63)) (PreH30 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH31 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH33 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (prio <> 63) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (1 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (1 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ ((Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))) = (task_suspend_updated_group (acquired) (target))) ” 
  &&  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTaskSuspend_entail_wit_4_1_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (1 = (task_suspend_self_byte (sg) (acquired) (tid))) ”
.

Definition OSTaskSuspend_entail_wit_4_1_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))) = (task_suspend_updated_group (acquired) (target))) ”
.

Definition OSTaskSuspend_entail_wit_4_1_split_goal_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
.

Definition OSTaskSuspend_entail_wit_4_1_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_entail_wit_4_2 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH6 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH11 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH12 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (task_suspend_target_facts sg acquired prio tid target )) (PreH15 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH16 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH20 : (task_suspend_target_facts sg acquired prio tid target )) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH22 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (prio <> 63)) (PreH27 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH28 : (0 <= prio)) (PreH29 : (prio <= 63)) (PreH30 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH31 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH33 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (prio <> 63) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (0 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ ((Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))) = (task_suspend_updated_group (acquired) (target))) ” 
  &&  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTaskSuspend_entail_wit_4_2_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (0 = (task_suspend_self_byte (sg) (acquired) (tid))) ”
.

Definition OSTaskSuspend_entail_wit_4_2_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))) = (task_suspend_updated_group (acquired) (target))) ”
.

Definition OSTaskSuspend_entail_wit_4_2_split_goal_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
.

Definition OSTaskSuspend_entail_wit_4_2_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_entail_wit_4_3 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (prio <> 63) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (1 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (1 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ ((os_sched_group (acquired)) = (task_suspend_updated_group (acquired) (target))) ” 
  &&  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTaskSuspend_entail_wit_4_3_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (1 = (task_suspend_self_byte (sg) (acquired) (tid))) ”
.

Definition OSTaskSuspend_entail_wit_4_3_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((os_sched_group (acquired)) = (task_suspend_updated_group (acquired) (target))) ”
.

Definition OSTaskSuspend_entail_wit_4_3_split_goal_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
.

Definition OSTaskSuspend_entail_wit_4_3_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_entail_wit_4_4 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (prio <> 63) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (0 = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ ((os_sched_group (acquired)) = (task_suspend_updated_group (acquired) (target))) ” 
  &&  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
  &&  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTaskSuspend_entail_wit_4_4_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (0 = (task_suspend_self_byte (sg) (acquired) (tid))) ”
.

Definition OSTaskSuspend_entail_wit_4_4_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((os_sched_group (acquired)) = (task_suspend_updated_group (acquired) (target))) ”
.

Definition OSTaskSuspend_entail_wit_4_4_split_goal_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ ((task_suspend_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
.

Definition OSTaskSuspend_entail_wit_4_4_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_entail_wit_5 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (encode_task_status ((stat (target)))))) (PreH4 : ((encode_task_status ((stat (target)))) <= 255)) (PreH5 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH6 : (prio <> 63)) (PreH7 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH8 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH10 : (task_suspend_target_facts sg acquired prio tid target )) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((stat (target)))) 8))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ” 
  &&  “ ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) )) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (encode_task_status ((stat (target)))))) (PreH3 : ((encode_task_status ((stat (target)))) <= 255)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (prio <> 63)) (PreH6 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH7 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH8 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((stat (target)))) 8))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) )) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
).

Definition OSTaskSuspend_entail_wit_5_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (encode_task_status ((stat (target)))))) (PreH3 : ((encode_task_status ((stat (target)))) <= 255)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (prio <> 63)) (PreH6 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH7 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH8 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((stat (target)))) 8))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) )) ”
.

Definition OSTaskSuspend_entail_wit_5_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (encode_task_status ((stat (target)))))) (PreH3 : ((encode_task_status ((stat (target)))) <= 255)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (prio <> 63)) (PreH6 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH7 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH8 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((stat (target)))) 8))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ”
.

Definition OSTaskSuspend_entail_wit_5_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (encode_task_status ((stat (target)))))) (PreH3 : ((encode_task_status ((stat (target)))) <= 255)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (prio <> 63)) (PreH6 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH7 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH8 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((stat (target)))) 8))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
.

Definition OSTaskSuspend_entail_wit_6 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH6 : ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) ))) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
|--
  EX (checkpoint_call: TaskSuspendCaller)  (checkpoint: UCOS2_Verify_State) ,
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ” 
  &&  “ (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint ) ” 
  &&  “ (task_suspend_scheduler_clients critical checkpoint_call ) ” 
  &&  “ ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint )) ” 
  &&  “ ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X )) ” 
  &&  “ ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X )) ”
  &&  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH6 : ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) ))) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
|--
  EX (checkpoint_call: TaskSuspendCaller)  (checkpoint: UCOS2_Verify_State) ,
  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ” 
  &&  “ (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint ) ” 
  &&  “ (task_suspend_scheduler_clients critical checkpoint_call ) ” 
  &&  “ ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint )) ” 
  &&  “ ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X )) ” 
  &&  “ ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X )) ”
  &&  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
).

Definition OSTaskSuspend_return_wit_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH3 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH8 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH9 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH10 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH11 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH12 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_refined_post environment critical saved_local sg checkpoint_call mask checkpoint 0 X )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 0 X )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH3 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH8 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH9 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH10 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH11 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH12 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_refined_post environment critical saved_local sg checkpoint_call mask checkpoint 0 X )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 0 X )
).

Definition OSTaskSuspend_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH3 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH8 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH9 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH10 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH11 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH12 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_refined_post environment critical saved_local sg checkpoint_call mask checkpoint 0 X )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 0 X )
.

Definition OSTaskSuspend_return_wit_2 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) <> 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 0 X )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) <> 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 0 X )
).

Definition OSTaskSuspend_return_wit_2_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) <> 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 0 X )
.

Definition OSTaskSuspend_return_wit_3 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 67 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (prio <> 63)) (PreH9 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH15 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 67 X )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 67 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (prio <> 63)) (PreH9 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH15 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 67 X )
).

Definition OSTaskSuspend_return_wit_3_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 67 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (prio <> 63)) (PreH9 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH15 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 67 X )
.

Definition OSTaskSuspend_return_wit_4 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 72 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 72 X )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 72 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 72 X )
).

Definition OSTaskSuspend_return_wit_4_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 72 0 acquired )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 72 X )
.

Definition OSTaskSuspend_return_wit_5 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 71 0 acquired )) (PreH3 : (prio = 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 71 X )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 71 0 acquired )) (PreH3 : (prio = 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 71 X )
).

Definition OSTaskSuspend_return_wit_5_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_step sg request priority acquired 71 0 acquired )) (PreH3 : (prio = 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_restore_history_post environment critical saved_local sg acquired_call cpu_sr acquired )
  **  (frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 71 X )
.

Definition OSTaskSuspend_return_wit_6 := 
(
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) <> 255)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 42 X )
) \/
(
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) <> 255)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 42 X )
).

Definition OSTaskSuspend_return_wit_6_split_goal_spatial := 
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) <> 255)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 42 X )
.

Definition OSTaskSuspend_return_wit_7 := 
(
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (prio_pre = 63)) (PreH2 : (prio_pre = request)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 71 X )
) \/
(
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (prio_pre = 63)) (PreH2 : (prio_pre = request)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 71 X )
).

Definition OSTaskSuspend_return_wit_7_split_goal_spatial := 
forall (prio_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (prio_pre = 63)) (PreH2 : (prio_pre = request)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame 71 X )
.

Definition OSTaskSuspend_partial_solve_wit_1_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (task_suspend_entry_facts sg request )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_entry_facts sg request ) ”
.

Definition OSTaskSuspend_partial_solve_wit_1_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (task_suspend_entry_facts sg request )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ”
  &&  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
.

Definition OSTaskSuspend_partial_solve_wit_1 := OSTaskSuspend_partial_solve_wit_1_pure -> OSTaskSuspend_partial_solve_wit_1_aux.

Definition OSTaskSuspend_partial_solve_wit_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (PreH1 : (task_suspend_entry_facts sg request )) (PreH2 : (task_suspend_completed_calls critical sg caller request mask before )) (PreH3 : (task_suspend_scheduler_clients critical caller )) (PreH4 : (task_suspend_entry_facts sg request )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_safe environment critical sg caller mask request before X )) ,
  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
|--
  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_completed_calls critical sg caller request mask before ) ” 
  &&  “ (task_suspend_scheduler_clients critical caller ) ” 
  &&  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_3_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (request <> priority)) (PreH2 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH6 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTaskSuspend_partial_solve_wit_3_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (request <> priority)) (PreH2 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH6 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (request <> priority) ” 
  &&  “ ((unsigned_last_nbits (request) (32)) <> 255) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_3 := OSTaskSuspend_partial_solve_wit_3_pure -> OSTaskSuspend_partial_solve_wit_3_aux.

Definition OSTaskSuspend_partial_solve_wit_4_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (request = priority)) (PreH2 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH6 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTaskSuspend_partial_solve_wit_4_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : (request = priority)) (PreH2 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH6 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (request = priority) ” 
  &&  “ ((unsigned_last_nbits (request) (32)) <> 255) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_4 := OSTaskSuspend_partial_solve_wit_4_pure -> OSTaskSuspend_partial_solve_wit_4_aux.

Definition OSTaskSuspend_partial_solve_wit_5_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH5 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTaskSuspend_partial_solve_wit_5_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (PreH1 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH5 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (frame )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits (request) (32)) = 255) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_5 := OSTaskSuspend_partial_solve_wit_5_pure -> OSTaskSuspend_partial_solve_wit_5_aux.

Definition OSTaskSuspend_partial_solve_wit_6_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (63 = 63) ” 
  &&  “ (63 = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ”
.

Definition OSTaskSuspend_partial_solve_wit_6_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
|--
  “ (63 = 63) ” 
  &&  “ (63 = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (prio = 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> 63)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_6 := OSTaskSuspend_partial_solve_wit_6_pure -> OSTaskSuspend_partial_solve_wit_6_aux.

Definition OSTaskSuspend_partial_solve_wit_7_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (63 = 63)) (PreH3 : (task_suspend_step sg request priority acquired 71 0 acquired )) (PreH4 : (prio = 63)) (PreH5 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH6 : (0 <= prio)) (PreH7 : (prio <= 63)) (PreH8 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH11 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> 63)
  **  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskSuspend_partial_solve_wit_7_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (63 = 63)) (PreH3 : (task_suspend_step sg request priority acquired 71 0 acquired )) (PreH4 : (prio = 63)) (PreH5 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH6 : (0 <= prio)) (PreH7 : (prio <= 63)) (PreH8 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH11 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_step sg request priority acquired 71 0 acquired ) ” 
  &&  “ (prio = 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_7 := OSTaskSuspend_partial_solve_wit_7_pure -> OSTaskSuspend_partial_solve_wit_7_aux.

Definition OSTaskSuspend_partial_solve_wit_8_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio <> 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ”
.

Definition OSTaskSuspend_partial_solve_wit_8_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio <> 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_8 := OSTaskSuspend_partial_solve_wit_8_pure -> OSTaskSuspend_partial_solve_wit_8_aux.

Definition OSTaskSuspend_partial_solve_wit_9_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio))) ”
.

Definition OSTaskSuspend_partial_solve_wit_9_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_9 := OSTaskSuspend_partial_solve_wit_9_pure -> OSTaskSuspend_partial_solve_wit_9_aux.

Definition OSTaskSuspend_partial_solve_wit_10_pure := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (prio <> 63)) (PreH7 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 = 0) ” 
  &&  “ (0 = (task_suspend_table_value (sg) (acquired) ((task_suspend_resolved_priority (sg) (request) (priority))))) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) <> 63) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (0 = (task_suspend_table_value (sg) (acquired) (prio))) ”
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 = (task_suspend_table_value (sg) (acquired) (prio))) ”
).

Definition OSTaskSuspend_partial_solve_wit_10_pure_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 = (task_suspend_table_value (sg) (acquired) (prio))) ”
.

Definition OSTaskSuspend_partial_solve_wit_10_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (prio <> 63)) (PreH7 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH13 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (0 = 0) ” 
  &&  “ (0 = (task_suspend_table_value (sg) (acquired) ((task_suspend_resolved_priority (sg) (request) (priority))))) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) <> 63) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (0 = (task_suspend_table_value (sg) (acquired) (prio))) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> (task_suspend_resolved_priority (sg) (request) (priority)))
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_10 := OSTaskSuspend_partial_solve_wit_10_pure -> OSTaskSuspend_partial_solve_wit_10_aux.

Definition OSTaskSuspend_partial_solve_wit_11_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (0 = 0)) (PreH3 : ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (task_suspend_step sg request priority acquired 72 0 acquired )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (prio <> 63)) (PreH10 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH11 : (0 <= prio)) (PreH12 : (prio <= 63)) (PreH13 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH16 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> (task_suspend_resolved_priority (sg) (request) (priority)))
  **  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskSuspend_partial_solve_wit_11_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (0 = 0)) (PreH3 : ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (task_suspend_step sg request priority acquired 72 0 acquired )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) = 0)) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (prio <> 63)) (PreH10 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH11 : (0 <= prio)) (PreH12 : (prio <= 63)) (PreH13 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH16 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_step sg request priority acquired 72 0 acquired ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_11 := OSTaskSuspend_partial_solve_wit_11_pure -> OSTaskSuspend_partial_solve_wit_11_aux.

Definition OSTaskSuspend_partial_solve_wit_12_pure := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (1 = 1) ” 
  &&  “ (1 = (task_suspend_table_value (sg) (acquired) ((task_suspend_resolved_priority (sg) (request) (priority))))) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) <> 63) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (1 = (task_suspend_table_value (sg) (acquired) (prio))) ”
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (prio <> 63)) (PreH9 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH15 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (1 = (task_suspend_table_value (sg) (acquired) (prio))) ”
).

Definition OSTaskSuspend_partial_solve_wit_12_pure_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (prio <> 63)) (PreH9 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH15 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (1 = (task_suspend_table_value (sg) (acquired) (prio))) ”
.

Definition OSTaskSuspend_partial_solve_wit_12_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (1 = 1) ” 
  &&  “ (1 = (task_suspend_table_value (sg) (acquired) ((task_suspend_resolved_priority (sg) (request) (priority))))) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) <> 63) ” 
  &&  “ ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (1 = (task_suspend_table_value (sg) (acquired) (prio))) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> 1)
  **  ((( &( "prio" ) )) # UChar  |-> (task_suspend_resolved_priority (sg) (request) (priority)))
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_12 := OSTaskSuspend_partial_solve_wit_12_pure -> OSTaskSuspend_partial_solve_wit_12_aux.

Definition OSTaskSuspend_partial_solve_wit_13_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (1 = 1)) (PreH3 : ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (task_suspend_step sg request priority acquired 67 0 acquired )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (prio <> 63)) (PreH11 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH12 : (0 <= prio)) (PreH13 : (prio <= 63)) (PreH14 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH17 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> 1)
  **  ((( &( "prio" ) )) # UChar  |-> (task_suspend_resolved_priority (sg) (request) (priority)))
  **  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskSuspend_partial_solve_wit_13_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (1 = 1)) (PreH3 : ((task_suspend_resolved_priority (sg) (request) (priority)) = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH4 : (task_suspend_step sg request priority acquired 67 0 acquired )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) = 1)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (prio <> 63)) (PreH11 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH12 : (0 <= prio)) (PreH13 : (prio <= 63)) (PreH14 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH17 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_step sg request priority acquired 67 0 acquired ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_13 := OSTaskSuspend_partial_solve_wit_13_pure -> OSTaskSuspend_partial_solve_wit_13_aux.

Definition OSTaskSuspend_partial_solve_wit_14_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH2 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio))) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 63) ”
.

Definition OSTaskSuspend_partial_solve_wit_14_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH2 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (prio <> 63)) (PreH8 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH14 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_table_value (sg) (acquired) (prio))) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 63) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_14 := OSTaskSuspend_partial_solve_wit_14_pure -> OSTaskSuspend_partial_solve_wit_14_aux.

Definition OSTaskSuspend_partial_solve_wit_15_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH4 : (task_suspend_target_facts sg acquired prio tid target )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (prio <> 63)) (PreH11 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH12 : (0 <= prio)) (PreH13 : (prio <= 63)) (PreH14 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH17 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_15_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH4 : (task_suspend_target_facts sg acquired prio tid target )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (prio <> 63)) (PreH11 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH12 : (0 <= prio)) (PreH13 : (prio <= 63)) (PreH14 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH17 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_15 := OSTaskSuspend_partial_solve_wit_15_pure -> OSTaskSuspend_partial_solve_wit_15_aux.

Definition OSTaskSuspend_partial_solve_wit_16_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH4 : (task_suspend_target_facts sg acquired prio tid target )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (prio <> 63)) (PreH11 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH12 : (0 <= prio)) (PreH13 : (prio <= 63)) (PreH14 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH17 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_16_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH4 : (task_suspend_target_facts sg acquired prio tid target )) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (prio <> 63)) (PreH11 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH12 : (0 <= prio)) (PreH13 : (prio <= 63)) (PreH14 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH17 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_16 := OSTaskSuspend_partial_solve_wit_16_pure -> OSTaskSuspend_partial_solve_wit_16_aux.

Definition OSTaskSuspend_partial_solve_wit_17_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (prio <> 63)) (PreH15 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH21 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_17_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (prio <> 63)) (PreH15 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH21 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_17 := OSTaskSuspend_partial_solve_wit_17_pure -> OSTaskSuspend_partial_solve_wit_17_aux.

Definition OSTaskSuspend_partial_solve_wit_18_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (prio <> 63)) (PreH15 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH21 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_18_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (prio <> 63)) (PreH15 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH21 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_18 := OSTaskSuspend_partial_solve_wit_18_pure -> OSTaskSuspend_partial_solve_wit_18_aux.

Definition OSTaskSuspend_partial_solve_wit_19_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (prio <> 63)) (PreH16 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH22 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
.

Definition OSTaskSuspend_partial_solve_wit_19_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (prio <> 63)) (PreH16 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH22 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_19 := OSTaskSuspend_partial_solve_wit_19_pure -> OSTaskSuspend_partial_solve_wit_19_aux.

Definition OSTaskSuspend_partial_solve_wit_20_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (prio <> 63)) (PreH16 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH22 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
.

Definition OSTaskSuspend_partial_solve_wit_20_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (prio <> 63)) (PreH16 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH22 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_20 := OSTaskSuspend_partial_solve_wit_20_pure -> OSTaskSuspend_partial_solve_wit_20_aux.

Definition OSTaskSuspend_partial_solve_wit_21 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_22 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : (prio <> 63)) (PreH20 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH21 : (0 <= prio)) (PreH22 : (prio <= 63)) (PreH23 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH26 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_23 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_24 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : (prio <> 63)) (PreH20 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH21 : (0 <= prio)) (PreH22 : (prio <= 63)) (PreH23 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH26 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_25_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : (prio <> 63)) (PreH20 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH21 : (0 <= prio)) (PreH22 : (prio <= 63)) (PreH23 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH26 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_25_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : (prio <> 63)) (PreH20 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH21 : (0 <= prio)) (PreH22 : (prio <= 63)) (PreH23 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH26 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_25 := OSTaskSuspend_partial_solve_wit_25_pure -> OSTaskSuspend_partial_solve_wit_25_aux.

Definition OSTaskSuspend_partial_solve_wit_26_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : (prio <> 63)) (PreH20 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH21 : (0 <= prio)) (PreH22 : (prio <= 63)) (PreH23 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH26 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_26_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : (prio <> 63)) (PreH20 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH21 : (0 <= prio)) (PreH22 : (prio <= 63)) (PreH23 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH24 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH26 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_26 := OSTaskSuspend_partial_solve_wit_26_pure -> OSTaskSuspend_partial_solve_wit_26_aux.

Definition OSTaskSuspend_partial_solve_wit_27 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_28 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_29_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_29_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_29 := OSTaskSuspend_partial_solve_wit_29_pure -> OSTaskSuspend_partial_solve_wit_29_aux.

Definition OSTaskSuspend_partial_solve_wit_30_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_30_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH2 : (task_suspend_target_facts sg acquired prio tid target )) (PreH3 : (task_suspend_target_facts sg acquired prio tid target )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (task_suspend_target_facts sg acquired prio tid target )) (PreH9 : (task_suspend_target_facts sg acquired prio tid target )) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_target_facts sg acquired prio tid target )) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (prio <> 63)) (PreH22 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH26 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH28 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_30 := OSTaskSuspend_partial_solve_wit_30_pure -> OSTaskSuspend_partial_solve_wit_30_aux.

Definition OSTaskSuspend_partial_solve_wit_31_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 0)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_31_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_31 := OSTaskSuspend_partial_solve_wit_31_pure -> OSTaskSuspend_partial_solve_wit_31_aux.

Definition OSTaskSuspend_partial_solve_wit_32_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
  **  ((( &( "self" ) )) # UChar  |-> 1)
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_32_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (tid: Z) (target: TaskAbstractState) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_target_facts sg acquired prio tid target )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH12 : (task_suspend_target_facts sg acquired prio tid target )) (PreH13 : (task_suspend_target_facts sg acquired prio tid target )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid)))) (PreH19 : (task_suspend_target_facts sg acquired prio tid target )) (PreH20 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 1)) (PreH21 : ((task_suspend_table_value (sg) (acquired) (prio)) <> 0)) (PreH22 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (prio <> 63)) (PreH26 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH30 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH32 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_suspend_current_pointer (sg) (acquired))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_suspend_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_32 := OSTaskSuspend_partial_solve_wit_32_pure -> OSTaskSuspend_partial_solve_wit_32_aux.

Definition OSTaskSuspend_partial_solve_wit_33_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (prio <> 63)) (PreH3 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH4 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ”
.

Definition OSTaskSuspend_partial_solve_wit_33_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (prio <> 63)) (PreH3 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH4 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH6 : (task_suspend_target_facts sg acquired prio tid target )) (PreH7 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH10 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (prio <> 63) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (y = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_suspend_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (task_suspend_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_33 := OSTaskSuspend_partial_solve_wit_33_pure -> OSTaskSuspend_partial_solve_wit_33_aux.

Definition OSTaskSuspend_partial_solve_wit_34_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH6 : ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) ))) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskSuspend_partial_solve_wit_34_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (PreH1 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH2 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH6 : ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) ))) (PreH7 : (task_suspend_safe environment critical sg caller mask request before X )) (PreH8 : (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired )) ,
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ” 
  &&  “ ((self = 1) -> (task_suspend_caller_source sg acquired_call (task_suspend_state (acquired) (tid) (target)) )) ” 
  &&  “ (task_suspend_safe environment critical sg caller mask request before X ) ” 
  &&  “ (task_suspend_save_effect environment critical sg caller acquired_call mask cpu_sr before acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired (task_suspend_state (acquired) (tid) (target)) )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_34 := OSTaskSuspend_partial_solve_wit_34_pure -> OSTaskSuspend_partial_solve_wit_34_aux.

Definition OSTaskSuspend_partial_solve_wit_35_pure := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_scheduler_clients critical checkpoint_call ) ” 
  &&  “ (task_suspend_caller_source sg checkpoint_call checkpoint ) ”
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH9 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH10 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH11 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH12 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH13 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_caller_source sg checkpoint_call checkpoint ) ”
).

Definition OSTaskSuspend_partial_solve_wit_35_pure_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH9 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH10 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH11 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH12 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH13 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_caller_source sg checkpoint_call checkpoint ) ”
.

Definition OSTaskSuspend_partial_solve_wit_35_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  “ (task_suspend_scheduler_clients critical checkpoint_call ) ” 
  &&  “ (task_suspend_caller_source sg checkpoint_call checkpoint ) ” 
  &&  “ ((unsigned_last_nbits (self) (32)) = 1) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ” 
  &&  “ (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint ) ” 
  &&  “ (task_suspend_scheduler_clients critical checkpoint_call ) ” 
  &&  “ ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint )) ” 
  &&  “ ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X )) ” 
  &&  “ ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X )) ”
  &&  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_35 := OSTaskSuspend_partial_solve_wit_35_pure -> OSTaskSuspend_partial_solve_wit_35_aux.

Definition OSTaskSuspend_partial_solve_wit_36_pure := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ) ”
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH9 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH10 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH11 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH12 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH13 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ) ”
).

Definition OSTaskSuspend_partial_solve_wit_36_pure_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH6 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH9 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH10 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH11 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH12 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH13 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "self" ) )) # UChar  |-> self)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ) ”
.

Definition OSTaskSuspend_partial_solve_wit_36_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (Z -> (UCOS2_Verify_State -> Prop))) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (tid: Z) (target: TaskAbstractState) (prio: Z) (self: Z) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (self) (32)) = 1)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (self = (task_suspend_self_byte (sg) (acquired) (tid)))) (PreH4 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) )) (PreH7 : (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint )) (PreH8 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH9 : ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint ))) (PreH10 : ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ))) (PreH11 : ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X ))) ,
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X ) ” 
  &&  “ ((unsigned_last_nbits (self) (32)) = 1) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (self = (task_suspend_self_byte (sg) (acquired) (tid))) ” 
  &&  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_step sg request priority acquired 0 self (task_suspend_state (acquired) (tid) (target)) ) ” 
  &&  “ (task_suspend_restore_observation critical sg acquired_call checkpoint_call (task_suspend_state (acquired) (tid) (target)) checkpoint ) ” 
  &&  “ (task_suspend_scheduler_clients critical checkpoint_call ) ” 
  &&  “ ((self = 1) -> (task_suspend_caller_source sg checkpoint_call checkpoint )) ” 
  &&  “ ((self = 1) -> (task_suspend_scheduler_safe environment critical sg checkpoint_call mask checkpoint 0 X )) ” 
  &&  “ ((self <> 1) -> (task_suspend_return_safe checkpoint 0 X )) ”
  &&  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
.

Definition OSTaskSuspend_partial_solve_wit_36 := OSTaskSuspend_partial_solve_wit_36_pure -> OSTaskSuspend_partial_solve_wit_36_aux.

Definition OSTaskSuspend_which_implies_wit_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_entry_facts sg request )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_entry_facts sg request ) ” 
  &&  “ (task_suspend_completed_calls critical sg caller request mask before ) ” 
  &&  “ (task_suspend_scheduler_clients critical caller ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_entry_facts sg request )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_scheduler_clients critical caller ) ” 
  &&  “ (task_suspend_completed_calls critical sg caller request mask before ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
).

Definition OSTaskSuspend_which_implies_wit_1_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_entry_facts sg request )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_scheduler_clients critical caller ) ”
.

Definition OSTaskSuspend_which_implies_wit_1_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_entry_facts sg request )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  “ (task_suspend_completed_calls critical sg caller request mask before ) ”
.

Definition OSTaskSuspend_which_implies_wit_1_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_entry_facts sg request )) ,
  (task_suspend_call_pre environment critical saved_local sg caller mask before request frame )
|--
  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
.

Definition OSTaskSuspend_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
|--
  (UCOS2_inv sg acquired )
).

Definition OSTaskSuspend_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (residual )
|--
  (UCOS2_inv sg acquired )
.

Definition OSTaskSuspend_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (prio = 63) ” 
  &&  “ (task_suspend_step sg request priority acquired 71 0 acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_step sg request priority acquired 71 0 acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
).

Definition OSTaskSuspend_which_implies_wit_3_split_goal_1 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_step sg request priority acquired 71 0 acquired ) ”
.

Definition OSTaskSuspend_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (PreH1 : (prio = 63)) (PreH2 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH3 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
.

Definition OSTaskSuspend_which_implies_wit_4 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (0 <= prio)) (PreH3 : (prio < 64)) ,
  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (0 <= prio)) (PreH3 : (prio < 64)) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
).

Definition OSTaskSuspend_which_implies_wit_4_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (0 <= prio)) (PreH3 : (prio < 64)) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
.

Definition OSTaskSuspend_which_implies_wit_4_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (0 <= prio)) (PreH3 : (prio < 64)) ,
  (UCOS2_inv sg acquired )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
.

Definition OSTaskSuspend_which_implies_wit_5 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (ptcb = (task_suspend_table_value (sg) (acquired) (prio))) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
|--
  (UCOS2_inv sg acquired )
).

Definition OSTaskSuspend_which_implies_wit_5_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_suspend_table_value (sg) (acquired) (prio)))
  **  (task_suspend_table_frame sg acquired prio )
|--
  (UCOS2_inv sg acquired )
.

Definition OSTaskSuspend_which_implies_wit_6 := 
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (ptcb = 0) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_step sg request priority acquired 72 0 acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_step sg request priority acquired 72 0 acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
).

Definition OSTaskSuspend_which_implies_wit_6_split_goal_1 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_step sg request priority acquired 72 0 acquired ) ”
.

Definition OSTaskSuspend_which_implies_wit_6_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
.

Definition OSTaskSuspend_which_implies_wit_7 := 
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual ) ” 
  &&  “ (ptcb = 1) ” 
  &&  “ (prio = (task_suspend_resolved_priority (sg) (request) (priority))) ” 
  &&  “ (task_suspend_step sg request priority acquired 67 0 acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
) \/
(
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_step sg request priority acquired 67 0 acquired ) ”
  &&  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
).

Definition OSTaskSuspend_which_implies_wit_7_split_goal_1 := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (task_suspend_step sg request priority acquired 67 0 acquired ) ”
.

Definition OSTaskSuspend_which_implies_wit_7_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_call: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (pointer: Z) (priority: Z) (residual: Assertion) (ptcb: Z) (prio: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (prio <> 63)) (PreH4 : (prio = (task_suspend_resolved_priority (sg) (request) (priority)))) (PreH5 : (task_suspend_acquired_facts critical sg caller request mask before cpu_sr acquired_call acquired pointer priority residual )) ,
  (task_suspend_tokens environment critical saved_local sg acquired_call cpu_sr acquired acquired )
  **  (UCOS2_inv sg acquired )
|--
  (task_suspend_masked environment critical saved_local sg acquired_call cpu_sr acquired acquired )
.

Definition OSTaskSuspend_which_implies_wit_8 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (ptcb <> 0)) (PreH4 : (ptcb <> 1)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 63)) ,
  (UCOS2_inv sg acquired )
|--
  EX (target: TaskAbstractState)  (tid: Z) ,
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_suspend_table_value (sg) (acquired) (prio)))) (PreH3 : (ptcb <> 0)) (PreH4 : (ptcb <> 1)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 63)) ,
  (UCOS2_inv sg acquired )
|--
  EX (target: TaskAbstractState)  (tid: Z) ,
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_target_facts sg acquired prio tid target ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_suspend_current_pointer (sg) (acquired)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
).

Definition OSTaskSuspend_which_implies_wit_9 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
).

Definition OSTaskSuspend_which_implies_wit_9_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
.

Definition OSTaskSuspend_which_implies_wit_9_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ”
.

Definition OSTaskSuspend_which_implies_wit_9_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
.

Definition OSTaskSuspend_which_implies_wit_10 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (task_public_storage sg (TskState (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
).

Definition OSTaskSuspend_which_implies_wit_10_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
.

Definition OSTaskSuspend_which_implies_wit_11 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (y = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (Znth (y) ((os_sched_rows (acquired))) (0)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
).

Definition OSTaskSuspend_which_implies_wit_11_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ”
.

Definition OSTaskSuspend_which_implies_wit_11_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ”
.

Definition OSTaskSuspend_which_implies_wit_11_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (y: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
.

Definition OSTaskSuspend_which_implies_wit_12 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (task_public_storage sg (TskState (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
|--
  (task_public_storage sg (TskState (acquired)) )
).

Definition OSTaskSuspend_which_implies_wit_12_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
|--
  (task_public_storage sg (TskState (acquired)) )
.

Definition OSTaskSuspend_which_implies_wit_13 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
).

Definition OSTaskSuspend_which_implies_wit_13_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ”
.

Definition OSTaskSuspend_which_implies_wit_13_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ”
.

Definition OSTaskSuspend_which_implies_wit_13_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
.

Definition OSTaskSuspend_which_implies_wit_14 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (task_public_storage sg (TskState (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
).

Definition OSTaskSuspend_which_implies_wit_14_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
.

Definition OSTaskSuspend_which_implies_wit_15 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (task_suspend_target_facts sg acquired prio tid target ) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (encode_task_status ((stat (target))))) ” 
  &&  “ ((encode_task_status ((stat (target)))) <= 255) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((encode_task_status ((stat (target)))) <= 255) ” 
  &&  “ (0 <= (encode_task_status ((stat (target))))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
).

Definition OSTaskSuspend_which_implies_wit_15_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((encode_task_status ((stat (target)))) <= 255) ”
.

Definition OSTaskSuspend_which_implies_wit_15_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (encode_task_status ((stat (target))))) ”
.

Definition OSTaskSuspend_which_implies_wit_15_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (prio: Z) (ptcb: Z) (PreH1 : (task_suspend_target_facts sg acquired prio tid target )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBStat)) )
.

Definition OSTaskSuspend_which_implies_wit_16 := 
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH2 : (task_suspend_caller_source sg checkpoint_call checkpoint )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
|--
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
) \/
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH2 : (task_suspend_caller_source sg checkpoint_call checkpoint )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
|--
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
).

Definition OSTaskSuspend_which_implies_wit_16_split_goal_spatial := 
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_scheduler_clients critical checkpoint_call )) (PreH2 : (task_suspend_caller_source sg checkpoint_call checkpoint )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
|--
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
.

Module Type VC_Correct.


Axiom proof_of_OSTaskSuspend_safety_wit_1 : OSTaskSuspend_safety_wit_1.
Axiom proof_of_OSTaskSuspend_safety_wit_2 : OSTaskSuspend_safety_wit_2.
Axiom proof_of_OSTaskSuspend_safety_wit_3 : OSTaskSuspend_safety_wit_3.
Axiom proof_of_OSTaskSuspend_safety_wit_4 : OSTaskSuspend_safety_wit_4.
Axiom proof_of_OSTaskSuspend_safety_wit_5 : OSTaskSuspend_safety_wit_5.
Axiom proof_of_OSTaskSuspend_safety_wit_6 : OSTaskSuspend_safety_wit_6.
Axiom proof_of_OSTaskSuspend_safety_wit_7 : OSTaskSuspend_safety_wit_7.
Axiom proof_of_OSTaskSuspend_safety_wit_8 : OSTaskSuspend_safety_wit_8.
Axiom proof_of_OSTaskSuspend_safety_wit_9 : OSTaskSuspend_safety_wit_9.
Axiom proof_of_OSTaskSuspend_entail_wit_1_1 : OSTaskSuspend_entail_wit_1_1.
Axiom proof_of_OSTaskSuspend_entail_wit_1_2 : OSTaskSuspend_entail_wit_1_2.
Axiom proof_of_OSTaskSuspend_entail_wit_2 : OSTaskSuspend_entail_wit_2.
Axiom proof_of_OSTaskSuspend_entail_wit_3_1 : OSTaskSuspend_entail_wit_3_1.
Axiom proof_of_OSTaskSuspend_entail_wit_3_2 : OSTaskSuspend_entail_wit_3_2.
Axiom proof_of_OSTaskSuspend_entail_wit_3_3 : OSTaskSuspend_entail_wit_3_3.
Axiom proof_of_OSTaskSuspend_entail_wit_4_1 : OSTaskSuspend_entail_wit_4_1.
Axiom proof_of_OSTaskSuspend_entail_wit_4_2 : OSTaskSuspend_entail_wit_4_2.
Axiom proof_of_OSTaskSuspend_entail_wit_4_3 : OSTaskSuspend_entail_wit_4_3.
Axiom proof_of_OSTaskSuspend_entail_wit_4_4 : OSTaskSuspend_entail_wit_4_4.
Axiom proof_of_OSTaskSuspend_entail_wit_5 : OSTaskSuspend_entail_wit_5.
Axiom proof_of_OSTaskSuspend_entail_wit_6 : OSTaskSuspend_entail_wit_6.
Axiom proof_of_OSTaskSuspend_return_wit_1 : OSTaskSuspend_return_wit_1.
Axiom proof_of_OSTaskSuspend_return_wit_2 : OSTaskSuspend_return_wit_2.
Axiom proof_of_OSTaskSuspend_return_wit_3 : OSTaskSuspend_return_wit_3.
Axiom proof_of_OSTaskSuspend_return_wit_4 : OSTaskSuspend_return_wit_4.
Axiom proof_of_OSTaskSuspend_return_wit_5 : OSTaskSuspend_return_wit_5.
Axiom proof_of_OSTaskSuspend_return_wit_6 : OSTaskSuspend_return_wit_6.
Axiom proof_of_OSTaskSuspend_return_wit_7 : OSTaskSuspend_return_wit_7.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_1_pure : OSTaskSuspend_partial_solve_wit_1_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_1 : OSTaskSuspend_partial_solve_wit_1.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_2 : OSTaskSuspend_partial_solve_wit_2.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_3_pure : OSTaskSuspend_partial_solve_wit_3_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_3 : OSTaskSuspend_partial_solve_wit_3.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_4_pure : OSTaskSuspend_partial_solve_wit_4_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_4 : OSTaskSuspend_partial_solve_wit_4.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_5_pure : OSTaskSuspend_partial_solve_wit_5_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_5 : OSTaskSuspend_partial_solve_wit_5.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_6_pure : OSTaskSuspend_partial_solve_wit_6_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_6 : OSTaskSuspend_partial_solve_wit_6.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_7_pure : OSTaskSuspend_partial_solve_wit_7_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_7 : OSTaskSuspend_partial_solve_wit_7.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_8_pure : OSTaskSuspend_partial_solve_wit_8_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_8 : OSTaskSuspend_partial_solve_wit_8.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_9_pure : OSTaskSuspend_partial_solve_wit_9_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_9 : OSTaskSuspend_partial_solve_wit_9.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_10_pure : OSTaskSuspend_partial_solve_wit_10_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_10 : OSTaskSuspend_partial_solve_wit_10.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_11_pure : OSTaskSuspend_partial_solve_wit_11_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_11 : OSTaskSuspend_partial_solve_wit_11.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_12_pure : OSTaskSuspend_partial_solve_wit_12_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_12 : OSTaskSuspend_partial_solve_wit_12.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_13_pure : OSTaskSuspend_partial_solve_wit_13_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_13 : OSTaskSuspend_partial_solve_wit_13.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_14_pure : OSTaskSuspend_partial_solve_wit_14_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_14 : OSTaskSuspend_partial_solve_wit_14.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_15_pure : OSTaskSuspend_partial_solve_wit_15_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_15 : OSTaskSuspend_partial_solve_wit_15.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_16_pure : OSTaskSuspend_partial_solve_wit_16_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_16 : OSTaskSuspend_partial_solve_wit_16.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_17_pure : OSTaskSuspend_partial_solve_wit_17_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_17 : OSTaskSuspend_partial_solve_wit_17.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_18_pure : OSTaskSuspend_partial_solve_wit_18_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_18 : OSTaskSuspend_partial_solve_wit_18.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_19_pure : OSTaskSuspend_partial_solve_wit_19_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_19 : OSTaskSuspend_partial_solve_wit_19.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_20_pure : OSTaskSuspend_partial_solve_wit_20_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_20 : OSTaskSuspend_partial_solve_wit_20.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_21 : OSTaskSuspend_partial_solve_wit_21.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_22 : OSTaskSuspend_partial_solve_wit_22.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_23 : OSTaskSuspend_partial_solve_wit_23.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_24 : OSTaskSuspend_partial_solve_wit_24.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_25_pure : OSTaskSuspend_partial_solve_wit_25_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_25 : OSTaskSuspend_partial_solve_wit_25.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_26_pure : OSTaskSuspend_partial_solve_wit_26_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_26 : OSTaskSuspend_partial_solve_wit_26.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_27 : OSTaskSuspend_partial_solve_wit_27.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_28 : OSTaskSuspend_partial_solve_wit_28.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_29_pure : OSTaskSuspend_partial_solve_wit_29_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_29 : OSTaskSuspend_partial_solve_wit_29.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_30_pure : OSTaskSuspend_partial_solve_wit_30_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_30 : OSTaskSuspend_partial_solve_wit_30.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_31_pure : OSTaskSuspend_partial_solve_wit_31_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_31 : OSTaskSuspend_partial_solve_wit_31.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_32_pure : OSTaskSuspend_partial_solve_wit_32_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_32 : OSTaskSuspend_partial_solve_wit_32.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_33_pure : OSTaskSuspend_partial_solve_wit_33_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_33 : OSTaskSuspend_partial_solve_wit_33.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_34_pure : OSTaskSuspend_partial_solve_wit_34_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_34 : OSTaskSuspend_partial_solve_wit_34.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_35_pure : OSTaskSuspend_partial_solve_wit_35_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_35 : OSTaskSuspend_partial_solve_wit_35.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_36_pure : OSTaskSuspend_partial_solve_wit_36_pure.
Axiom proof_of_OSTaskSuspend_partial_solve_wit_36 : OSTaskSuspend_partial_solve_wit_36.
Axiom proof_of_OSTaskSuspend_which_implies_wit_1 : OSTaskSuspend_which_implies_wit_1.
Axiom proof_of_OSTaskSuspend_which_implies_wit_2 : OSTaskSuspend_which_implies_wit_2.
Axiom proof_of_OSTaskSuspend_which_implies_wit_3 : OSTaskSuspend_which_implies_wit_3.
Axiom proof_of_OSTaskSuspend_which_implies_wit_4 : OSTaskSuspend_which_implies_wit_4.
Axiom proof_of_OSTaskSuspend_which_implies_wit_5 : OSTaskSuspend_which_implies_wit_5.
Axiom proof_of_OSTaskSuspend_which_implies_wit_6 : OSTaskSuspend_which_implies_wit_6.
Axiom proof_of_OSTaskSuspend_which_implies_wit_7 : OSTaskSuspend_which_implies_wit_7.
Axiom proof_of_OSTaskSuspend_which_implies_wit_8 : OSTaskSuspend_which_implies_wit_8.
Axiom proof_of_OSTaskSuspend_which_implies_wit_9 : OSTaskSuspend_which_implies_wit_9.
Axiom proof_of_OSTaskSuspend_which_implies_wit_10 : OSTaskSuspend_which_implies_wit_10.
Axiom proof_of_OSTaskSuspend_which_implies_wit_11 : OSTaskSuspend_which_implies_wit_11.
Axiom proof_of_OSTaskSuspend_which_implies_wit_12 : OSTaskSuspend_which_implies_wit_12.
Axiom proof_of_OSTaskSuspend_which_implies_wit_13 : OSTaskSuspend_which_implies_wit_13.
Axiom proof_of_OSTaskSuspend_which_implies_wit_14 : OSTaskSuspend_which_implies_wit_14.
Axiom proof_of_OSTaskSuspend_which_implies_wit_15 : OSTaskSuspend_which_implies_wit_15.
Axiom proof_of_OSTaskSuspend_which_implies_wit_16 : OSTaskSuspend_which_implies_wit_16.

End VC_Correct.
