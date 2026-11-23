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
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_call_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSSchedUnlock -----*)

Definition OSSchedUnlock_safety_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) = 1)) (PreH4 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (os_sched_unlock_continuation external critical sg context before X )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH8 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_inside_frame external platform critical sg context retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedUnlock_safety_wit_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_continuation external critical sg context before X )) (PreH3 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH4 : ((os_sched_unlock_requests (entry)) = true)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedUnlock_safety_wit_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedUnlock_safety_wit_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedUnlock_safety_wit_5 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedUnlock_entail_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) = 1)) (PreH4 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (os_sched_unlock_continuation external critical sg context before X )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH8 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_inside_frame external platform critical sg context retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask retval before entry ) ” 
  &&  “ (0 <= (os_sched_ints (entry))) ” 
  &&  “ ((os_sched_ints (entry)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (entry))) ” 
  &&  “ ((os_sched_locks (entry)) <= 255) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) = 1)) (PreH4 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (os_sched_unlock_continuation external critical sg context before X )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH8 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_inside_frame external platform critical sg context retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask retval before entry ) ” 
  &&  “ (0 <= (os_sched_ints (entry))) ” 
  &&  “ ((os_sched_ints (entry)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (entry))) ” 
  &&  “ ((os_sched_locks (entry)) <= 255) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
).

Definition OSSchedUnlock_entail_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_locks (entry_2)) > 0)) (PreH2 : ((os_sched_ints (entry_2)) = 0)) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH6 : (0 <= (os_sched_ints (entry_2)))) (PreH7 : ((os_sched_ints (entry_2)) <= 255)) (PreH8 : (0 <= (os_sched_locks (entry_2)))) (PreH9 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((os_sched_locks (entry_2)) - 1 ))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_ints (entry)) = 0) ” 
  &&  “ (0 < (os_sched_locks (entry))) ” 
  &&  “ ((os_sched_locks (entry)) <= 255) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_unlock_counted_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_locks (entry_2)) > 0)) (PreH2 : ((os_sched_ints (entry_2)) = 0)) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH6 : (0 <= (os_sched_ints (entry_2)))) (PreH7 : ((os_sched_ints (entry_2)) <= 255)) (PreH8 : (0 <= (os_sched_locks (entry_2)))) (PreH9 : ((os_sched_locks (entry_2)) <= 255)) ,
  TT && emp 
|--
  “ (((os_sched_locks (entry_2)) - 1 ) = (os_sched_unlock_counted_locks (entry_2))) ”
  &&  emp
).

Definition OSSchedUnlock_entail_wit_2_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_locks (entry_2)) > 0)) (PreH2 : ((os_sched_ints (entry_2)) = 0)) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH6 : (0 <= (os_sched_ints (entry_2)))) (PreH7 : ((os_sched_ints (entry_2)) <= 255)) (PreH8 : (0 <= (os_sched_locks (entry_2)))) (PreH9 : ((os_sched_locks (entry_2)) <= 255)) ,
  (((os_sched_locks (entry_2)) - 1 ) = (os_sched_unlock_counted_locks (entry_2)))
.

Definition OSSchedUnlock_entail_wit_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_counted_locks (entry_2))) (32)) = 0)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH5 : ((os_sched_ints (entry_2)) = 0)) (PreH6 : (0 < (os_sched_locks (entry_2)))) (PreH7 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_unlock_counted_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = true) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_counted_locks (entry_2))) (32)) = 0)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH5 : ((os_sched_ints (entry_2)) = 0)) (PreH6 : (0 < (os_sched_locks (entry_2)))) (PreH7 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_unlock_counted_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = true) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
).

Definition OSSchedUnlock_entail_wit_4 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_continuation external critical sg context before X )) (PreH3 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH4 : ((os_sched_unlock_requests (entry_2)) = true)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry_2)) )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = true) ”
  &&  (os_sched_pre external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_continuation external critical sg context before X )) (PreH3 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH4 : ((os_sched_unlock_requests (entry_2)) = true)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry_2)) )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = true) ”
  &&  (os_sched_pre external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
).

Definition OSSchedUnlock_entail_wit_5 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_counted_locks (entry_2))) (32)) <> 0)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH5 : ((os_sched_ints (entry_2)) = 0)) (PreH6 : (0 < (os_sched_locks (entry_2)))) (PreH7 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_unlock_counted_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_counted_locks (entry_2))) (32)) <> 0)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH5 : ((os_sched_ints (entry_2)) = 0)) (PreH6 : (0 < (os_sched_locks (entry_2)))) (PreH7 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_unlock_counted_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
).

Definition OSSchedUnlock_entail_wit_6 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_locks (entry_2)) <= 0)) (PreH2 : ((os_sched_ints (entry_2)) = 0)) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH6 : (0 <= (os_sched_ints (entry_2)))) (PreH7 : ((os_sched_ints (entry_2)) <= 255)) (PreH8 : (0 <= (os_sched_locks (entry_2)))) (PreH9 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_locks (entry_2)) <= 0)) (PreH2 : ((os_sched_ints (entry_2)) = 0)) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH6 : (0 <= (os_sched_ints (entry_2)))) (PreH7 : ((os_sched_ints (entry_2)) <= 255)) (PreH8 : (0 <= (os_sched_locks (entry_2)))) (PreH9 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
).

Definition OSSchedUnlock_entail_wit_7 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_ints (entry_2)) <> 0)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH5 : (0 <= (os_sched_ints (entry_2)))) (PreH6 : ((os_sched_ints (entry_2)) <= 255)) (PreH7 : (0 <= (os_sched_locks (entry_2)))) (PreH8 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_ints (entry_2)) <> 0)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry_2 )) (PreH5 : (0 <= (os_sched_ints (entry_2)))) (PreH6 : ((os_sched_ints (entry_2)) <= 255)) (PreH7 : (0 <= (os_sched_locks (entry_2)))) (PreH8 : ((os_sched_locks (entry_2)) <= 255)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
).

Definition OSSchedUnlock_return_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH6 : ((os_sched_unlock_requests (entry)) = true)) ,
  (os_sched_post external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH6 : ((os_sched_unlock_requests (entry)) = true)) ,
  (os_sched_post external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
).

Definition OSSchedUnlock_return_wit_1_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (os_sched_unlock_continuation external critical sg context before X )) (PreH5 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH6 : ((os_sched_unlock_requests (entry)) = true)) ,
  (os_sched_post external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
.

Definition OSSchedUnlock_return_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
).

Definition OSSchedUnlock_return_wit_2_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
.

Definition OSSchedUnlock_return_wit_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
).

Definition OSSchedUnlock_return_wit_3_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
.

Definition OSSchedUnlock_return_wit_4 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
).

Definition OSSchedUnlock_return_wit_4_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_outside_frame external platform critical sg context (armv7a_irq_fiq_mask (cpu_sr)) (os_sched_unlock_checkpoint (true) (entry)) )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
.

Definition OSSchedUnlock_return_wit_5 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) <> 1)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) <> 1)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
).

Definition OSSchedUnlock_return_wit_5_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) <> 1)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
|--
  (os_sched_unlock_program_post external platform critical sg context mask before X )
.

Definition OSSchedUnlock_partial_solve_wit_1_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSSchedUnlock_partial_solve_wit_1_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_program_pre external platform critical sg context mask before X )
.

Definition OSSchedUnlock_partial_solve_wit_1 := OSSchedUnlock_partial_solve_wit_1_pure -> OSSchedUnlock_partial_solve_wit_1_aux.

Definition OSSchedUnlock_partial_solve_wit_2_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) = 1)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSSchedUnlock_partial_solve_wit_2_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) = 1)) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_unlock_acquire_safety external critical sg context before )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((os_sched_unlock_running (before))) (32)) = 1) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_unlock_acquire_safety external critical sg context before ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
.

Definition OSSchedUnlock_partial_solve_wit_2 := OSSchedUnlock_partial_solve_wit_2_pure -> OSSchedUnlock_partial_solve_wit_2_aux.

Definition OSSchedUnlock_partial_solve_wit_3_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_continuation external critical sg context before X )) (PreH3 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH4 : ((os_sched_unlock_requests (entry)) = true)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSSchedUnlock_partial_solve_wit_3_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_unlock_continuation external critical sg context before X )) (PreH3 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH4 : ((os_sched_unlock_requests (entry)) = true)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = true) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
.

Definition OSSchedUnlock_partial_solve_wit_3 := OSSchedUnlock_partial_solve_wit_3_pure -> OSSchedUnlock_partial_solve_wit_3_aux.

Definition OSSchedUnlock_partial_solve_wit_4_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH5 : ((os_sched_unlock_requests (entry)) = true)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_pre external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSSchedUnlock_partial_solve_wit_4_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (os_sched_unlock_continuation external critical sg context before X )) (PreH4 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH5 : ((os_sched_unlock_requests (entry)) = true)) ,
  (os_sched_pre external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = true) ”
  &&  (os_sched_pre external platform critical sg context mask (os_sched_unlock_checkpoint (true) (entry)) )
.

Definition OSSchedUnlock_partial_solve_wit_4 := OSSchedUnlock_partial_solve_wit_4_pure -> OSSchedUnlock_partial_solve_wit_4_aux.

Definition OSSchedUnlock_partial_solve_wit_5_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSSchedUnlock_partial_solve_wit_5_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
.

Definition OSSchedUnlock_partial_solve_wit_5 := OSSchedUnlock_partial_solve_wit_5_pure -> OSSchedUnlock_partial_solve_wit_5_aux.

Definition OSSchedUnlock_partial_solve_wit_6_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSSchedUnlock_partial_solve_wit_6_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
.

Definition OSSchedUnlock_partial_solve_wit_6 := OSSchedUnlock_partial_solve_wit_6_pure -> OSSchedUnlock_partial_solve_wit_6_aux.

Definition OSSchedUnlock_partial_solve_wit_7_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSSchedUnlock_partial_solve_wit_7_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_unlock_continuation external critical sg context before X )) (PreH2 : (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry )) (PreH3 : ((os_sched_unlock_requests (entry)) = false)) ,
  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (os_sched_unlock_body_facts external critical sg context mask cpu_sr before entry ) ” 
  &&  “ ((os_sched_unlock_requests (entry)) = false) ”
  &&  (os_sched_unlock_inside_frame external platform critical sg context cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_unlock_checkpoint (true) (entry)) )
.

Definition OSSchedUnlock_partial_solve_wit_7 := OSSchedUnlock_partial_solve_wit_7_pure -> OSSchedUnlock_partial_solve_wit_7_aux.

Definition OSSchedUnlock_which_implies_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_unlock_acquire_safety external critical sg context before ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (os_sched_unlock_acquire_safety external critical sg context before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_unlock_continuation external critical sg context before X ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
).

Definition OSSchedUnlock_which_implies_wit_1_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (os_sched_unlock_acquire_safety external critical sg context before ) ”
.

Definition OSSchedUnlock_which_implies_wit_1_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSSchedUnlock_which_implies_wit_1_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  “ (os_sched_unlock_continuation external critical sg context before X ) ”
.

Definition OSSchedUnlock_which_implies_wit_1_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_program_pre external platform critical sg context mask before X )
|--
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_unlock_running (before)))
  **  (os_sched_unlock_observation_frame external platform critical sg context mask before )
.

Module Type VC_Correct.


Axiom proof_of_OSSchedUnlock_safety_wit_1 : OSSchedUnlock_safety_wit_1.
Axiom proof_of_OSSchedUnlock_safety_wit_2 : OSSchedUnlock_safety_wit_2.
Axiom proof_of_OSSchedUnlock_safety_wit_3 : OSSchedUnlock_safety_wit_3.
Axiom proof_of_OSSchedUnlock_safety_wit_4 : OSSchedUnlock_safety_wit_4.
Axiom proof_of_OSSchedUnlock_safety_wit_5 : OSSchedUnlock_safety_wit_5.
Axiom proof_of_OSSchedUnlock_entail_wit_1 : OSSchedUnlock_entail_wit_1.
Axiom proof_of_OSSchedUnlock_entail_wit_2 : OSSchedUnlock_entail_wit_2.
Axiom proof_of_OSSchedUnlock_entail_wit_3 : OSSchedUnlock_entail_wit_3.
Axiom proof_of_OSSchedUnlock_entail_wit_4 : OSSchedUnlock_entail_wit_4.
Axiom proof_of_OSSchedUnlock_entail_wit_5 : OSSchedUnlock_entail_wit_5.
Axiom proof_of_OSSchedUnlock_entail_wit_6 : OSSchedUnlock_entail_wit_6.
Axiom proof_of_OSSchedUnlock_entail_wit_7 : OSSchedUnlock_entail_wit_7.
Axiom proof_of_OSSchedUnlock_return_wit_1 : OSSchedUnlock_return_wit_1.
Axiom proof_of_OSSchedUnlock_return_wit_2 : OSSchedUnlock_return_wit_2.
Axiom proof_of_OSSchedUnlock_return_wit_3 : OSSchedUnlock_return_wit_3.
Axiom proof_of_OSSchedUnlock_return_wit_4 : OSSchedUnlock_return_wit_4.
Axiom proof_of_OSSchedUnlock_return_wit_5 : OSSchedUnlock_return_wit_5.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_1_pure : OSSchedUnlock_partial_solve_wit_1_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_1 : OSSchedUnlock_partial_solve_wit_1.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_2_pure : OSSchedUnlock_partial_solve_wit_2_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_2 : OSSchedUnlock_partial_solve_wit_2.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_3_pure : OSSchedUnlock_partial_solve_wit_3_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_3 : OSSchedUnlock_partial_solve_wit_3.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_4_pure : OSSchedUnlock_partial_solve_wit_4_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_4 : OSSchedUnlock_partial_solve_wit_4.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_5_pure : OSSchedUnlock_partial_solve_wit_5_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_5 : OSSchedUnlock_partial_solve_wit_5.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_6_pure : OSSchedUnlock_partial_solve_wit_6_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_6 : OSSchedUnlock_partial_solve_wit_6.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_7_pure : OSSchedUnlock_partial_solve_wit_7_pure.
Axiom proof_of_OSSchedUnlock_partial_solve_wit_7 : OSSchedUnlock_partial_solve_wit_7.
Axiom proof_of_OSSchedUnlock_which_implies_wit_1 : OSSchedUnlock_which_implies_wit_1.

End VC_Correct.
