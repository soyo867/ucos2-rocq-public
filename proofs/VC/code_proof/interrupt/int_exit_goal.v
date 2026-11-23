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
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSIntExit -----*)

Definition OSIntExit_safety_wit_1 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (os_int_exit_body_facts external port critical sg context mask retval before entry )) (PreH2 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH3 : (os_int_exit_continuation external port critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context retval entry )
  **  (os_sched_work_cells sg entry (os_sched_old_high (entry)) (os_sched_old_pointer (sg) (entry)) (os_sched_counter (entry)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSIntExit_safety_wit_2 := 
forall (cpu_sr: Z) (PreH1 : (0 = 1)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ False ”
.

Definition OSIntExit_safety_wit_3 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_requests_switch (true) (entry)) = false)) ,
  (os_int_exit_post platform port critical sg context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSIntExit_entail_wit_1_1 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (entry_3)) > 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_ints (entry_3)))) (PreH5 : ((os_sched_ints (entry_3)) <= 255)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_body_facts external port critical sg context mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH10 : (os_int_exit_continuation external port critical sg context before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH13 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH14 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context retval entry_3 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((os_sched_ints (entry_3)) - 1 ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_3)))
  **  (sched_new_rep sg (os_sched_group (entry_3)) (os_sched_rows (entry_3)) (os_sched_old_high (entry_3)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_3)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_3)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_3)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_3)))
  **  (os_sched_work_frame sg entry_3 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask retval before entry ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_int_exit_inside_frame platform port critical sg context retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (entry_3)) > 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_ints (entry_3)))) (PreH5 : ((os_sched_ints (entry_3)) <= 255)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_body_facts external port critical sg context mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH10 : (os_int_exit_continuation external port critical sg context before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH13 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH14 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (((os_sched_ints (entry_3)) - 1 ) = (os_int_exit_counted_ints (entry_3))) ”
  &&  emp
).

Definition OSIntExit_entail_wit_1_1_split_goal_1 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (entry_3)) > 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_ints (entry_3)))) (PreH5 : ((os_sched_ints (entry_3)) <= 255)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_body_facts external port critical sg context mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH10 : (os_int_exit_continuation external port critical sg context before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH13 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH14 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (((os_sched_ints (entry_3)) - 1 ) = (os_int_exit_counted_ints (entry_3)))
.

Definition OSIntExit_entail_wit_1_2 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (entry_3)) <= 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_ints (entry_3)))) (PreH5 : ((os_sched_ints (entry_3)) <= 255)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_body_facts external port critical sg context mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH10 : (os_int_exit_continuation external port critical sg context before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH13 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH14 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context retval entry_3 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_3)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_3)))
  **  (sched_new_rep sg (os_sched_group (entry_3)) (os_sched_rows (entry_3)) (os_sched_old_high (entry_3)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_3)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_3)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_3)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_3)))
  **  (os_sched_work_frame sg entry_3 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask retval before entry ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_int_exit_inside_frame platform port critical sg context retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (entry_3)) <= 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_ints (entry_3)))) (PreH5 : ((os_sched_ints (entry_3)) <= 255)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_body_facts external port critical sg context mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH10 : (os_int_exit_continuation external port critical sg context before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH13 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH14 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((os_sched_ints (entry_3)) = (os_int_exit_counted_ints (entry_3))) ”
  &&  emp
).

Definition OSIntExit_entail_wit_1_2_split_goal_1 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (entry_3)) <= 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_ints (entry_3)))) (PreH5 : ((os_sched_ints (entry_3)) <= 255)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_body_facts external port critical sg context mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH10 : (os_int_exit_continuation external port critical sg context before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH13 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH14 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((os_sched_ints (entry_3)) = (os_int_exit_counted_ints (entry_3)))
.

Definition OSIntExit_entail_wit_2 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry_2))) (32)) = 0)) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_counted_ints (entry)) = 0) ” 
  &&  “ ((os_sched_locks (entry)) = 0) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <= (os_sched_selected (entry))) ” 
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry)) (os_sched_rows (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry_2))) (32)) = 0)) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((os_sched_table (sg) (entry_2)) = (os_sched_table (sg) (entry))) ” 
  &&  “ ((os_sched_counter (entry_2)) = (os_sched_counter (entry))) ” 
  &&  “ ((os_sched_old_pointer (sg) (entry_2)) = (os_sched_old_pointer (sg) (entry))) ” 
  &&  “ ((os_sched_current (entry_2)) = (os_sched_current (entry))) ” 
  &&  “ ((os_sched_locks (entry_2)) = (os_sched_locks (entry))) ” 
  &&  “ ((os_int_exit_counted_ints (entry_2)) = (os_int_exit_counted_ints (entry))) ” 
  &&  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_counted_ints (entry)) = 0) ” 
  &&  “ ((os_sched_locks (entry)) = 0) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <= (os_sched_selected (entry))) ” 
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry)) (os_sched_rows (entry)) )
  **  (os_sched_work_frame sg entry )
).

Definition OSIntExit_entail_wit_3 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH4 : ((os_int_exit_counted_ints (entry_2)) = 0)) (PreH5 : ((os_sched_locks (entry_2)) = 0)) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (0 <= (os_sched_selected (entry_2)))) (PreH8 : ((os_sched_selected (entry_2)) < 64)) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  (os_int_exit_transfer_program_pre external platform port critical sg context cpu_sr before entry X )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH6 : ((os_int_exit_counted_ints (entry_2)) = 0)) (PreH7 : ((os_sched_locks (entry_2)) = 0)) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (0 <= (os_sched_selected (entry_2)))) (PreH10 : ((os_sched_selected (entry_2)) < 64)) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  (os_int_exit_transfer_program_pre external platform port critical sg context cpu_sr before entry X )
).

Definition OSIntExit_entail_wit_4_1 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH4 : ((os_int_exit_counted_ints (entry_2)) = 0)) (PreH5 : ((os_sched_locks (entry_2)) = 0)) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (0 <= (os_sched_selected (entry_2)))) (PreH8 : ((os_sched_selected (entry_2)) < 64)) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH6 : ((os_int_exit_counted_ints (entry_2)) = 0)) (PreH7 : ((os_sched_locks (entry_2)) = 0)) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (0 <= (os_sched_selected (entry_2)))) (PreH10 : ((os_sched_selected (entry_2)) < 64)) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
).

Definition OSIntExit_entail_wit_4_2 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH2 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry_2))) (32)) = 0)) (PreH3 : (os_int_exit_continuation external port critical sg context before X )) (PreH4 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH4 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry_2))) (32)) = 0)) (PreH5 : (os_int_exit_continuation external port critical sg context before X )) (PreH6 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH7 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
).

Definition OSIntExit_entail_wit_4_3 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry_2))) (32)) <> 0)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH4 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH5 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry_2))) (32)) <> 0)) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
).

Definition OSIntExit_return_wit_1 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_requests_switch (true) (entry)) = false)) ,
  (os_int_exit_post platform port critical sg context mask before )
|--
  (os_int_exit_program_post platform port critical sg context mask before X )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_requests_switch (true) (entry)) = false)) ,
  (os_int_exit_post platform port critical sg context mask before )
|--
  (os_int_exit_program_post platform port critical sg context mask before X )
).

Definition OSIntExit_return_wit_1_split_goal_spatial := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_requests_switch (true) (entry)) = false)) ,
  (os_int_exit_post platform port critical sg context mask before )
|--
  (os_int_exit_program_post platform port critical sg context mask before X )
.

Definition OSIntExit_return_wit_2 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) <> 1)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
|--
  (os_int_exit_program_post platform port critical sg context mask before X )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) <> 1)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
|--
  (os_int_exit_program_post platform port critical sg context mask before X )
).

Definition OSIntExit_return_wit_2_split_goal_spatial := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) <> 1)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
|--
  (os_int_exit_program_post platform port critical sg context mask before X )
.

Definition OSIntExit_partial_solve_wit_1_pure := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSIntExit_partial_solve_wit_1_aux := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_int_exit_program_pre external platform port critical sg context mask before X )
.

Definition OSIntExit_partial_solve_wit_1 := OSIntExit_partial_solve_wit_1_pure -> OSIntExit_partial_solve_wit_1_aux.

Definition OSIntExit_partial_solve_wit_2_pure := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_int_exit_acquire_safety external port critical sg context before ) ” 
  &&  “ ((os_int_exit_running (before)) = 1) ”
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH7 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ ((os_int_exit_running (before)) = 1) ”
).

Definition OSIntExit_partial_solve_wit_2_pure_split_goal_1 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH4 : (os_int_exit_continuation external port critical sg context before X )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH7 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ ((os_int_exit_running (before)) = 1) ”
.

Definition OSIntExit_partial_solve_wit_2_aux := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH2 : (os_int_exit_continuation external port critical sg context before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_int_exit_acquire_safety external port critical sg context before ) ” 
  &&  “ ((os_int_exit_running (before)) = 1) ” 
  &&  “ ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1) ” 
  &&  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_int_exit_acquire_safety external port critical sg context before ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
.

Definition OSIntExit_partial_solve_wit_2 := OSIntExit_partial_solve_wit_2_pure -> OSIntExit_partial_solve_wit_2_aux.

Definition OSIntExit_partial_solve_wit_3_pure := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (os_int_exit_body_facts external port critical sg context mask retval before entry )) (PreH2 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH3 : (os_int_exit_continuation external port critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context retval entry )
  **  (os_sched_work_cells sg entry (os_sched_old_high (entry)) (os_sched_old_pointer (sg) (entry)) (os_sched_counter (entry)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask retval before entry ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSIntExit_partial_solve_wit_3_aux := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (os_int_exit_body_facts external port critical sg context mask retval before entry )) (PreH2 : ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1)) (PreH3 : (os_int_exit_continuation external port critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_int_exit_acquire_safety external port critical sg context before )) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH7 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context retval entry )
  **  (os_sched_work_cells sg entry (os_sched_old_high (entry)) (os_sched_old_pointer (sg) (entry)) (os_sched_counter (entry)) )
|--
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask retval before entry ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask retval before entry ) ” 
  &&  “ ((unsigned_last_nbits ((os_int_exit_running (before))) (32)) = 1) ” 
  &&  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_int_exit_acquire_safety external port critical sg context before ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_int_exit_inside_frame platform port critical sg context retval entry )
  **  (os_sched_work_cells sg entry (os_sched_old_high (entry)) (os_sched_old_pointer (sg) (entry)) (os_sched_counter (entry)) )
.

Definition OSIntExit_partial_solve_wit_3 := OSIntExit_partial_solve_wit_3_pure -> OSIntExit_partial_solve_wit_3_aux.

Definition OSIntExit_partial_solve_wit_4_pure := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry))) (32)) = 0)) (PreH3 : (os_int_exit_continuation external port critical sg context before X )) (PreH4 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OSIntExit_partial_solve_wit_4_aux := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_int_exit_counted_ints (entry))) (32)) = 0)) (PreH3 : (os_int_exit_continuation external port critical sg context before X )) (PreH4 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH5 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((os_int_exit_counted_ints (entry))) (32)) = 0) ” 
  &&  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
.

Definition OSIntExit_partial_solve_wit_4 := OSIntExit_partial_solve_wit_4_pure -> OSIntExit_partial_solve_wit_4_aux.

Definition OSIntExit_partial_solve_wit_5 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_counted_ints (entry)) = 0)) (PreH4 : ((os_sched_locks (entry)) = 0)) (PreH5 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (0 <= (os_sched_selected (entry)))) (PreH7 : ((os_sched_selected (entry)) < 64)) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry)) (os_sched_rows (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_counted_ints (entry)) = 0) ” 
  &&  “ ((os_sched_locks (entry)) = 0) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <= (os_sched_selected (entry))) ” 
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((os_sched_selected (entry)) * sizeof(PTR)))) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (os_sched_selected (entry)) 0 64 (os_sched_table (sg) (entry)) )
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_exit_counted_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_int_exit_ready_tables sg (os_sched_group (entry)) (os_sched_rows (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
.

Definition OSIntExit_partial_solve_wit_6 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) ,
  (os_int_exit_transfer_program_pre external platform port critical sg context cpu_sr before entry X )
|--
  (os_int_exit_transfer_program_pre external platform port critical sg context cpu_sr before entry X )
.

Definition OSIntExit_partial_solve_wit_7_pure := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_requests_switch (true) (entry)) = false)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
.

Definition OSIntExit_partial_solve_wit_7_aux := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry )) (PreH3 : ((os_int_exit_requests_switch (true) (entry)) = false)) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ” 
  &&  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_int_exit_requests_switch (true) (entry)) = false) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_int_exit_ready_checkpoint (true) (entry)) )
  **  (unmap_table_rep sg )
.

Definition OSIntExit_partial_solve_wit_7 := OSIntExit_partial_solve_wit_7_pure -> OSIntExit_partial_solve_wit_7_aux.

Definition OSIntExit_which_implies_wit_1 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_int_exit_acquire_safety external port critical sg context before ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_acquire_safety external port critical sg context before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_int_exit_continuation external port critical sg context before X ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
).

Definition OSIntExit_which_implies_wit_1_split_goal_1 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OSIntExit_which_implies_wit_1_split_goal_2 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (os_int_exit_acquire_safety external port critical sg context before ) ”
.

Definition OSIntExit_which_implies_wit_1_split_goal_3 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSIntExit_which_implies_wit_1_split_goal_4 := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  “ (os_int_exit_continuation external port critical sg context before X ) ”
.

Definition OSIntExit_which_implies_wit_1_split_goal_spatial := 
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_program_pre external platform port critical sg context mask before X )
|--
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_exit_running (before)))
  **  (os_int_exit_outside_frame platform port critical sg context mask before )
.

Definition OSIntExit_which_implies_wit_2 := 
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH3 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH4 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  (os_sched_work_cells sg entry_2 (os_sched_old_high (entry_2)) (os_sched_old_pointer (sg) (entry_2)) (os_sched_counter (entry_2)) )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ (0 <= (os_sched_ints (entry))) ” 
  &&  “ ((os_sched_ints (entry)) <= 255) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
) \/
(
forall (X: (OsIntExitOutcome -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsIntExitCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (port: OsIntExitPlatformResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_int_exit_continuation external port critical sg context before X )) (PreH2 : (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry_2 )) (PreH3 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH4 : (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry_2 )
  **  (os_sched_work_cells sg entry_2 (os_sched_old_high (entry_2)) (os_sched_old_pointer (sg) (entry_2)) (os_sched_counter (entry_2)) )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_int_exit_continuation external port critical sg context before X ) ” 
  &&  “ (os_int_exit_body_facts external port critical sg context mask cpu_sr before entry ) ” 
  &&  “ (0 <= (os_sched_ints (entry))) ” 
  &&  “ ((os_sched_ints (entry)) <= 255) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_int_exit_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_int_exit_inside_frame platform port critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
).

Module Type VC_Correct.


Axiom proof_of_OSIntExit_safety_wit_1 : OSIntExit_safety_wit_1.
Axiom proof_of_OSIntExit_safety_wit_2 : OSIntExit_safety_wit_2.
Axiom proof_of_OSIntExit_safety_wit_3 : OSIntExit_safety_wit_3.
Axiom proof_of_OSIntExit_entail_wit_1_1 : OSIntExit_entail_wit_1_1.
Axiom proof_of_OSIntExit_entail_wit_1_2 : OSIntExit_entail_wit_1_2.
Axiom proof_of_OSIntExit_entail_wit_2 : OSIntExit_entail_wit_2.
Axiom proof_of_OSIntExit_entail_wit_3 : OSIntExit_entail_wit_3.
Axiom proof_of_OSIntExit_entail_wit_4_1 : OSIntExit_entail_wit_4_1.
Axiom proof_of_OSIntExit_entail_wit_4_2 : OSIntExit_entail_wit_4_2.
Axiom proof_of_OSIntExit_entail_wit_4_3 : OSIntExit_entail_wit_4_3.
Axiom proof_of_OSIntExit_return_wit_1 : OSIntExit_return_wit_1.
Axiom proof_of_OSIntExit_return_wit_2 : OSIntExit_return_wit_2.
Axiom proof_of_OSIntExit_partial_solve_wit_1_pure : OSIntExit_partial_solve_wit_1_pure.
Axiom proof_of_OSIntExit_partial_solve_wit_1 : OSIntExit_partial_solve_wit_1.
Axiom proof_of_OSIntExit_partial_solve_wit_2_pure : OSIntExit_partial_solve_wit_2_pure.
Axiom proof_of_OSIntExit_partial_solve_wit_2 : OSIntExit_partial_solve_wit_2.
Axiom proof_of_OSIntExit_partial_solve_wit_3_pure : OSIntExit_partial_solve_wit_3_pure.
Axiom proof_of_OSIntExit_partial_solve_wit_3 : OSIntExit_partial_solve_wit_3.
Axiom proof_of_OSIntExit_partial_solve_wit_4_pure : OSIntExit_partial_solve_wit_4_pure.
Axiom proof_of_OSIntExit_partial_solve_wit_4 : OSIntExit_partial_solve_wit_4.
Axiom proof_of_OSIntExit_partial_solve_wit_5 : OSIntExit_partial_solve_wit_5.
Axiom proof_of_OSIntExit_partial_solve_wit_6 : OSIntExit_partial_solve_wit_6.
Axiom proof_of_OSIntExit_partial_solve_wit_7_pure : OSIntExit_partial_solve_wit_7_pure.
Axiom proof_of_OSIntExit_partial_solve_wit_7 : OSIntExit_partial_solve_wit_7.
Axiom proof_of_OSIntExit_which_implies_wit_1 : OSIntExit_which_implies_wit_1.
Axiom proof_of_OSIntExit_which_implies_wit_2 : OSIntExit_which_implies_wit_2.

End VC_Correct.
