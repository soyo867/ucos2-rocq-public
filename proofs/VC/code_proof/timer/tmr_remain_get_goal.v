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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_remain_get_spec.
               Import UCOS2_C_Rules.
               Local Open Scope sac_scope.
Local Open Scope sac.

(*----- Function OSTmrRemainGet -----*)

Definition OSTmrRemainGet_safety_wit_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = p)) (PreH2 : (perr_pre = error_addr)) (PreH3 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH4 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH5 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrRemainGet_entail_wit_1 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_state (current)) = 3)) (PreH3 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH4 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((tmr_remain_get_ints (before)) = 0)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : ((tmr_remain_get_ints (before)) <= 0)) (PreH11 : (ty = 100)) (PreH12 : (p <> 0)) (PreH13 : (0 <= ty)) (PreH14 : (ty <= 255)) (PreH15 : (0 <= (tmr_remain_get_ints (before)))) (PreH16 : ((tmr_remain_get_ints (before)) <= 255)) (PreH17 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH18 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH19 : (ptmr_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (perr_pre = error_addr)) (PreH22 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH23 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH24 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH27 : (3 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_remain_get_match (current)))
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> (tmr_remain_get_time (locked)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (unsigned_last_nbits (((tmr_remain_get_match (current)) - (tmr_remain_get_time (locked)) )) (32)) 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_time (locked)) <= UINT_MAX)) (PreH2 : ((tmr_remain_get_match (current)) <= UINT_MAX)) (PreH3 : ((tmr_remain_get_time (locked)) >= 0)) (PreH4 : ((tmr_remain_get_match (current)) >= 0)) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : ((tmr_remain_get_state (current)) = 3)) (PreH7 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH8 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((tmr_remain_get_ints (before)) = 0)) (PreH12 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH13 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH14 : ((tmr_remain_get_ints (before)) <= 0)) (PreH15 : (ty = 100)) (PreH16 : (p <> 0)) (PreH17 : (0 <= ty)) (PreH18 : (ty <= 255)) (PreH19 : (0 <= (tmr_remain_get_ints (before)))) (PreH20 : ((tmr_remain_get_ints (before)) <= 255)) (PreH21 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH22 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH23 : (ptmr_pre <> 0)) (PreH24 : (ptmr_pre = p)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH27 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH28 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH31 : (3 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_remain_get_match (current)))
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> (tmr_remain_get_time (locked)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (unsigned_last_nbits (((tmr_remain_get_match (current)) - (tmr_remain_get_time (locked)) )) (32)) 0 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_2_1 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_option (current)) = 2)) (PreH3 : ((tmr_remain_get_delay (current)) = 0)) (PreH4 : ((tmr_remain_get_delay (current)) = 0)) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : ((tmr_remain_get_state (current)) = 1)) (PreH7 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH8 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((tmr_remain_get_ints (before)) = 0)) (PreH12 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH13 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH14 : ((tmr_remain_get_ints (before)) <= 0)) (PreH15 : (ty = 100)) (PreH16 : (p <> 0)) (PreH17 : (0 <= ty)) (PreH18 : (ty <= 255)) (PreH19 : (0 <= (tmr_remain_get_ints (before)))) (PreH20 : ((tmr_remain_get_ints (before)) <= 255)) (PreH21 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH22 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH23 : (ptmr_pre <> 0)) (PreH24 : (ptmr_pre = p)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH27 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH28 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH31 : (3 <> (tmr_remain_get_state (current)))) (PreH32 : (1 = (tmr_remain_get_state (current)))) (PreH33 : (2 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_remain_get_period (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_period (current)) 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) <= UINT_MAX)) (PreH2 : ((tmr_remain_get_period (current)) <= UINT_MAX)) (PreH3 : ((tmr_remain_get_delay (current)) >= 0)) (PreH4 : ((tmr_remain_get_period (current)) >= 0)) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : ((tmr_remain_get_option (current)) = 2)) (PreH7 : ((tmr_remain_get_delay (current)) = 0)) (PreH8 : ((tmr_remain_get_delay (current)) = 0)) (PreH9 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH10 : ((tmr_remain_get_state (current)) = 1)) (PreH11 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH12 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH13 : (p <> 0)) (PreH14 : (ty = 100)) (PreH15 : ((tmr_remain_get_ints (before)) = 0)) (PreH16 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH17 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH18 : ((tmr_remain_get_ints (before)) <= 0)) (PreH19 : (ty = 100)) (PreH20 : (p <> 0)) (PreH21 : (0 <= ty)) (PreH22 : (ty <= 255)) (PreH23 : (0 <= (tmr_remain_get_ints (before)))) (PreH24 : ((tmr_remain_get_ints (before)) <= 255)) (PreH25 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH26 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH31 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH32 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH35 : (3 <> (tmr_remain_get_state (current)))) (PreH36 : (1 = (tmr_remain_get_state (current)))) (PreH37 : (2 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_remain_get_period (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_period (current)) 0 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_2_2 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : ((tmr_remain_get_state (current)) = 1)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((tmr_remain_get_ints (before)) = 0)) (PreH9 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH10 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH11 : ((tmr_remain_get_ints (before)) <= 0)) (PreH12 : (ty = 100)) (PreH13 : (p <> 0)) (PreH14 : (0 <= ty)) (PreH15 : (ty <= 255)) (PreH16 : (0 <= (tmr_remain_get_ints (before)))) (PreH17 : ((tmr_remain_get_ints (before)) <= 255)) (PreH18 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr_pre = p)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH24 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH25 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH26 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH28 : (3 <> (tmr_remain_get_state (current)))) (PreH29 : (1 = (tmr_remain_get_state (current)))) (PreH30 : (2 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_delay (current)) 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) <= UINT_MAX)) (PreH2 : ((tmr_remain_get_delay (current)) >= 0)) (PreH3 : ((tmr_remain_get_delay (current)) <> 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : ((tmr_remain_get_state (current)) = 1)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH8 : (p <> 0)) (PreH9 : (ty = 100)) (PreH10 : ((tmr_remain_get_ints (before)) = 0)) (PreH11 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH12 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH13 : ((tmr_remain_get_ints (before)) <= 0)) (PreH14 : (ty = 100)) (PreH15 : (p <> 0)) (PreH16 : (0 <= ty)) (PreH17 : (ty <= 255)) (PreH18 : (0 <= (tmr_remain_get_ints (before)))) (PreH19 : ((tmr_remain_get_ints (before)) <= 255)) (PreH20 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH22 : (ptmr_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (perr_pre = error_addr)) (PreH25 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH26 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH27 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH28 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH30 : (3 <> (tmr_remain_get_state (current)))) (PreH31 : (1 = (tmr_remain_get_state (current)))) (PreH32 : (2 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_delay (current)) 0 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_3_1 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_state (current)) = 1)) (PreH3 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH4 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((tmr_remain_get_ints (before)) = 0)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : ((tmr_remain_get_ints (before)) <= 0)) (PreH11 : (ty = 100)) (PreH12 : (p <> 0)) (PreH13 : (0 <= ty)) (PreH14 : (ty <= 255)) (PreH15 : (0 <= (tmr_remain_get_ints (before)))) (PreH16 : ((tmr_remain_get_ints (before)) <= 255)) (PreH17 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH18 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH19 : (ptmr_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (perr_pre = error_addr)) (PreH22 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH23 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH24 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH27 : (3 <> (tmr_remain_get_state (current)))) (PreH28 : (1 = (tmr_remain_get_state (current)))) (PreH29 : (2 <> (tmr_remain_get_option (current)))) (PreH30 : (1 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_delay (current)) 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) <= UINT_MAX)) (PreH2 : ((tmr_remain_get_delay (current)) >= 0)) (PreH3 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH4 : ((tmr_remain_get_state (current)) = 1)) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((tmr_remain_get_ints (before)) = 0)) (PreH10 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH11 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH12 : ((tmr_remain_get_ints (before)) <= 0)) (PreH13 : (ty = 100)) (PreH14 : (p <> 0)) (PreH15 : (0 <= ty)) (PreH16 : (ty <= 255)) (PreH17 : (0 <= (tmr_remain_get_ints (before)))) (PreH18 : ((tmr_remain_get_ints (before)) <= 255)) (PreH19 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH20 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (ptmr_pre = p)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH25 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH26 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH29 : (3 <> (tmr_remain_get_state (current)))) (PreH30 : (1 = (tmr_remain_get_state (current)))) (PreH31 : (2 <> (tmr_remain_get_option (current)))) (PreH32 : (1 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_delay (current)) 0 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_3_2 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_state (current)) = 1)) (PreH3 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH4 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((tmr_remain_get_ints (before)) = 0)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : ((tmr_remain_get_ints (before)) <= 0)) (PreH11 : (ty = 100)) (PreH12 : (p <> 0)) (PreH13 : (0 <= ty)) (PreH14 : (ty <= 255)) (PreH15 : (0 <= (tmr_remain_get_ints (before)))) (PreH16 : ((tmr_remain_get_ints (before)) <= 255)) (PreH17 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH18 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH19 : (ptmr_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (perr_pre = error_addr)) (PreH22 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH23 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH24 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH27 : (3 <> (tmr_remain_get_state (current)))) (PreH28 : (1 = (tmr_remain_get_state (current)))) (PreH29 : (2 <> (tmr_remain_get_option (current)))) (PreH30 : (1 <> (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_delay (current)) 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) <= UINT_MAX)) (PreH2 : ((tmr_remain_get_delay (current)) >= 0)) (PreH3 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH4 : ((tmr_remain_get_state (current)) = 1)) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((tmr_remain_get_ints (before)) = 0)) (PreH10 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH11 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH12 : ((tmr_remain_get_ints (before)) <= 0)) (PreH13 : (ty = 100)) (PreH14 : (p <> 0)) (PreH15 : (0 <= ty)) (PreH16 : (ty <= 255)) (PreH17 : (0 <= (tmr_remain_get_ints (before)))) (PreH18 : ((tmr_remain_get_ints (before)) <= 255)) (PreH19 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH20 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (ptmr_pre = p)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH25 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH26 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH29 : (3 <> (tmr_remain_get_state (current)))) (PreH30 : (1 = (tmr_remain_get_state (current)))) (PreH31 : (2 <> (tmr_remain_get_option (current)))) (PreH32 : (1 <> (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current (tmr_remain_get_delay (current)) 0 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_4_1 := 
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
) \/
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
).

Definition OSTmrRemainGet_entail_wit_4_1_split_goal_spatial := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
.

Definition OSTmrRemainGet_entail_wit_4_2 := 
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
) \/
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
).

Definition OSTmrRemainGet_entail_wit_4_2_split_goal_spatial := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
.

Definition OSTmrRemainGet_entail_wit_5 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 <> (tmr_remain_get_state (current)))) (PreH27 : (2 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 <> (tmr_remain_get_state (current)))) (PreH27 : (2 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_6 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 <> (tmr_remain_get_state (current)))) (PreH27 : (2 <> (tmr_remain_get_state (current)))) (PreH28 : (0 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 <> (tmr_remain_get_state (current)))) (PreH27 : (2 <> (tmr_remain_get_state (current)))) (PreH28 : (0 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
  **  (F )
).

Definition OSTmrRemainGet_entail_wit_7 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 <> (tmr_remain_get_state (current)))) (PreH27 : (2 <> (tmr_remain_get_state (current)))) (PreH28 : (0 <> (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 <> (tmr_remain_get_state (current)))) (PreH27 : (2 <> (tmr_remain_get_state (current)))) (PreH28 : (0 <> (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
  **  (F )
).

Definition OSTmrRemainGet_return_wit_1 := 
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 141)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
) \/
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 141)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
).

Definition OSTmrRemainGet_return_wit_1_split_goal_spatial := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 141)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
.

Definition OSTmrRemainGet_return_wit_2 := 
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 135)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
) \/
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 135)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
).

Definition OSTmrRemainGet_return_wit_2_split_goal_spatial := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 135)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
.

Definition OSTmrRemainGet_return_wit_3 := 
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
) \/
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
).

Definition OSTmrRemainGet_return_wit_3_split_goal_spatial := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
.

Definition OSTmrRemainGet_return_wit_4 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (remain: Z) ,
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
.

Definition OSTmrRemainGet_return_wit_5 := 
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
) \/
(
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
).

Definition OSTmrRemainGet_return_wit_5_split_goal_spatial := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |-> 0)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr remain F X )
.

Definition OSTmrRemainGet_return_wit_6 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((tmr_remain_get_ints (before)) > 0)) (PreH2 : (ty = 100)) (PreH3 : (p <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (tmr_remain_get_ints (before)))) (PreH7 : ((tmr_remain_get_ints (before)) <= 255)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH15 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((tmr_remain_get_ints (before)) > 0)) (PreH2 : (ty = 100)) (PreH3 : (p <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (tmr_remain_get_ints (before)))) (PreH7 : ((tmr_remain_get_ints (before)) <= 255)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH15 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
).

Definition OSTmrRemainGet_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((tmr_remain_get_ints (before)) > 0)) (PreH2 : (ty = 100)) (PreH3 : (p <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (tmr_remain_get_ints (before)))) (PreH7 : ((tmr_remain_get_ints (before)) <= 255)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH15 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
.

Definition OSTmrRemainGet_return_wit_7 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ty <> 100)) (PreH2 : (p <> 0)) (PreH3 : (0 <= ty)) (PreH4 : (ty <= 255)) (PreH5 : (0 <= (tmr_remain_get_ints (before)))) (PreH6 : ((tmr_remain_get_ints (before)) <= 255)) (PreH7 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH8 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH9 : (ptmr_pre <> 0)) (PreH10 : (ptmr_pre = p)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH13 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH14 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH15 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |-> 137)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ty <> 100)) (PreH2 : (p <> 0)) (PreH3 : (0 <= ty)) (PreH4 : (ty <= 255)) (PreH5 : (0 <= (tmr_remain_get_ints (before)))) (PreH6 : ((tmr_remain_get_ints (before)) <= 255)) (PreH7 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH8 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH9 : (ptmr_pre <> 0)) (PreH10 : (ptmr_pre = p)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH13 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH14 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH15 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |-> 137)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
).

Definition OSTmrRemainGet_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ty <> 100)) (PreH2 : (p <> 0)) (PreH3 : (0 <= ty)) (PreH4 : (ty <= 255)) (PreH5 : (0 <= (tmr_remain_get_ints (before)))) (PreH6 : ((tmr_remain_get_ints (before)) <= 255)) (PreH7 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH8 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH9 : (ptmr_pre <> 0)) (PreH10 : (ptmr_pre = p)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH13 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH14 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH15 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |-> 137)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
.

Definition OSTmrRemainGet_return_wit_8 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH6 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |-> 138)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH6 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |-> 138)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
).

Definition OSTmrRemainGet_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH6 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |-> 138)
  **  (F )
|--
  (tmr_remain_get_post external platform critical sg context mask raw p ty original i before error_addr 0 F X )
.

Definition OSTmrRemainGet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH6 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ”
.

Definition OSTmrRemainGet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH6 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_1 := OSTmrRemainGet_partial_solve_wit_1_pure -> OSTmrRemainGet_partial_solve_wit_1_aux.

Definition OSTmrRemainGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((tmr_remain_get_ints (before)) <= 0)) (PreH2 : (ty = 100)) (PreH3 : (p <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (tmr_remain_get_ints (before)))) (PreH7 : ((tmr_remain_get_ints (before)) <= 255)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH15 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((tmr_remain_get_ints (before)) <= 0)) (PreH2 : (ty = 100)) (PreH3 : (p <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (tmr_remain_get_ints (before)))) (PreH7 : ((tmr_remain_get_ints (before)) <= 255)) (PreH8 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH9 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH15 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_2 := OSTmrRemainGet_partial_solve_wit_2_pure -> OSTmrRemainGet_partial_solve_wit_2_aux.

Definition OSTmrRemainGet_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH6 : ((tmr_remain_get_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (p <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (tmr_remain_get_ints (before)))) (PreH12 : ((tmr_remain_get_ints (before)) <= 255)) (PreH13 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH20 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH6 : ((tmr_remain_get_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (p <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (tmr_remain_get_ints (before)))) (PreH12 : ((tmr_remain_get_ints (before)) <= 255)) (PreH13 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH20 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
).

Definition OSTmrRemainGet_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH6 : ((tmr_remain_get_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (p <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (tmr_remain_get_ints (before)))) (PreH12 : ((tmr_remain_get_ints (before)) <= 255)) (PreH13 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH20 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH6 : ((tmr_remain_get_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (p <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (tmr_remain_get_ints (before)))) (PreH12 : ((tmr_remain_get_ints (before)) <= 255)) (PreH13 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH20 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_3 := OSTmrRemainGet_partial_solve_wit_3_pure -> OSTmrRemainGet_partial_solve_wit_3_aux.

Definition OSTmrRemainGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH6 : ((tmr_remain_get_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (p <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (tmr_remain_get_ints (before)))) (PreH12 : ((tmr_remain_get_ints (before)) <= 255)) (PreH13 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH20 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH6 : ((tmr_remain_get_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (p <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (tmr_remain_get_ints (before)))) (PreH12 : ((tmr_remain_get_ints (before)) <= 255)) (PreH13 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH14 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH20 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_4 := OSTmrRemainGet_partial_solve_wit_4_pure -> OSTmrRemainGet_partial_solve_wit_4_aux.

Definition OSTmrRemainGet_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 = (tmr_remain_get_state (current)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ ((tmr_remain_get_state (current)) = 3) ”
.

Definition OSTmrRemainGet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ ((tmr_remain_get_state (current)) = 3) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ” 
  &&  “ (3 = (tmr_remain_get_state (current))) ”
  &&  (tmr_remain_get_payload sg p current locked )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_5 := OSTmrRemainGet_partial_solve_wit_5_pure -> OSTmrRemainGet_partial_solve_wit_5_aux.

Definition OSTmrRemainGet_partial_solve_wit_6 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_7_pure := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "remain" ) )) # UInt  |-> remain)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_7_aux := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_7 := OSTmrRemainGet_partial_solve_wit_7_pure -> OSTmrRemainGet_partial_solve_wit_7_aux.

Definition OSTmrRemainGet_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 = (tmr_remain_get_state (current)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_state (current)) = 1) ”
.

Definition OSTmrRemainGet_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((tmr_remain_get_ints (before)) = 0)) (PreH6 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH7 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH8 : ((tmr_remain_get_ints (before)) <= 0)) (PreH9 : (ty = 100)) (PreH10 : (p <> 0)) (PreH11 : (0 <= ty)) (PreH12 : (ty <= 255)) (PreH13 : (0 <= (tmr_remain_get_ints (before)))) (PreH14 : ((tmr_remain_get_ints (before)) <= 255)) (PreH15 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH16 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH17 : (ptmr_pre <> 0)) (PreH18 : (ptmr_pre = p)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH21 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH23 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH25 : (3 <> (tmr_remain_get_state (current)))) (PreH26 : (1 = (tmr_remain_get_state (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_state (current)) = 1) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ” 
  &&  “ (3 <> (tmr_remain_get_state (current))) ” 
  &&  “ (1 = (tmr_remain_get_state (current))) ”
  &&  (tmr_remain_get_payload sg p current locked )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_8 := OSTmrRemainGet_partial_solve_wit_8_pure -> OSTmrRemainGet_partial_solve_wit_8_aux.

Definition OSTmrRemainGet_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) = 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : ((tmr_remain_get_state (current)) = 1)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((tmr_remain_get_ints (before)) = 0)) (PreH9 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH10 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH11 : ((tmr_remain_get_ints (before)) <= 0)) (PreH12 : (ty = 100)) (PreH13 : (p <> 0)) (PreH14 : (0 <= ty)) (PreH15 : (ty <= 255)) (PreH16 : (0 <= (tmr_remain_get_ints (before)))) (PreH17 : ((tmr_remain_get_ints (before)) <= 255)) (PreH18 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr_pre = p)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH24 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH25 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH26 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH28 : (3 <> (tmr_remain_get_state (current)))) (PreH29 : (1 = (tmr_remain_get_state (current)))) (PreH30 : (2 = (tmr_remain_get_option (current)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "remain" ) )) # UInt  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_option (current)) = 2) ” 
  &&  “ ((tmr_remain_get_delay (current)) = 0) ”
.

Definition OSTmrRemainGet_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : ((tmr_remain_get_delay (current)) = 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : ((tmr_remain_get_state (current)) = 1)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((tmr_remain_get_ints (before)) = 0)) (PreH9 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH10 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH11 : ((tmr_remain_get_ints (before)) <= 0)) (PreH12 : (ty = 100)) (PreH13 : (p <> 0)) (PreH14 : (0 <= ty)) (PreH15 : (ty <= 255)) (PreH16 : (0 <= (tmr_remain_get_ints (before)))) (PreH17 : ((tmr_remain_get_ints (before)) <= 255)) (PreH18 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH19 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr_pre = p)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH24 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH25 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH26 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) (PreH28 : (3 <> (tmr_remain_get_state (current)))) (PreH29 : (1 = (tmr_remain_get_state (current)))) (PreH30 : (2 = (tmr_remain_get_option (current)))) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_option (current)) = 2) ” 
  &&  “ ((tmr_remain_get_delay (current)) = 0) ” 
  &&  “ ((tmr_remain_get_delay (current)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_state (current)) = 1) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_remain_get_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrDly") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg))) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ” 
  &&  “ (3 <> (tmr_remain_get_state (current))) ” 
  &&  “ (1 = (tmr_remain_get_state (current))) ” 
  &&  “ (2 = (tmr_remain_get_option (current))) ”
  &&  (tmr_remain_get_period_storage p current )
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_9 := OSTmrRemainGet_partial_solve_wit_9_pure -> OSTmrRemainGet_partial_solve_wit_9_aux.

Definition OSTmrRemainGet_partial_solve_wit_10 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_11_pure := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "remain" ) )) # UInt  |-> remain)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_11_aux := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_11 := OSTmrRemainGet_partial_solve_wit_11_pure -> OSTmrRemainGet_partial_solve_wit_11_aux.

Definition OSTmrRemainGet_partial_solve_wit_12_pure := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "remain" ) )) # UInt  |-> remain)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_12_aux := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (remain: Z) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_12 := OSTmrRemainGet_partial_solve_wit_12_pure -> OSTmrRemainGet_partial_solve_wit_12_aux.

Definition OSTmrRemainGet_partial_solve_wit_13 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_14 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_15_pure := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
  **  ((( &( "remain" ) )) # UInt  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_15_aux := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_15 := OSTmrRemainGet_partial_solve_wit_15_pure -> OSTmrRemainGet_partial_solve_wit_15_aux.

Definition OSTmrRemainGet_partial_solve_wit_16 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_17_pure := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
  **  ((( &( "remain" ) )) # UInt  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_17_aux := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_17 := OSTmrRemainGet_partial_solve_wit_17_pure -> OSTmrRemainGet_partial_solve_wit_17_aux.

Definition OSTmrRemainGet_partial_solve_wit_18_pure := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
  **  ((( &( "remain" ) )) # UInt  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrRemainGet_partial_solve_wit_18_aux := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_partial_solve_wit_18 := OSTmrRemainGet_partial_solve_wit_18_pure -> OSTmrRemainGet_partial_solve_wit_18_aux.

Definition OSTmrRemainGet_partial_solve_wit_19 := 
forall (X: (TmrRemainGetOutput -> (UCOS2_Verify_State -> Prop))) (F: Assertion) (error_addr: Z) (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (tmr_remain_get_safe external critical sg context raw p ty original i before X )) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_remain_get_safe external critical sg context raw p ty original i before X ) ”
  &&  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
  **  ((error_addr) # UChar  |->_)
  **  (F )
.

Definition OSTmrRemainGet_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ (p <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ” 
  &&  “ ((tmr_remain_get_ints (before)) <= 255) ” 
  &&  “ (0 <= (tmr_remain_get_ints (before))) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= ty) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
).

Definition OSTmrRemainGet_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ”
.

Definition OSTmrRemainGet_which_implies_wit_1_split_goal_2 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ ((tmr_remain_get_ints (before)) <= 255) ”
.

Definition OSTmrRemainGet_which_implies_wit_1_split_goal_3 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ (0 <= (tmr_remain_get_ints (before))) ”
.

Definition OSTmrRemainGet_which_implies_wit_1_split_goal_4 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ (ty <= 255) ”
.

Definition OSTmrRemainGet_which_implies_wit_1_split_goal_5 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  “ (0 <= ty) ”
.

Definition OSTmrRemainGet_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH3 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) ,
  (tmr_remain_get_input external platform critical sg context mask raw p ty original i before )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
.

Definition OSTmrRemainGet_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((tmr_remain_get_ints (before)) = 0) ” 
  &&  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_entry_facts external critical sg context raw p ty original i before ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
).

Definition OSTmrRemainGet_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (( &( "OSIntNesting" ) ) = (tmr_remain_get_int_address (sg)))) (PreH5 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH6 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_remain_get_ints (before)))
  **  (tmr_remain_get_observation_rest sg raw p ty original i before )
  **  (tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints (before)) )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
.

Definition OSTmrRemainGet_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  EX (acquired: UCOS2_Verify_State)  (locked: UCOS2_Verify_State)  (current: TimerImage) ,
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((tmr_remain_get_ints (before)) = 0)) (PreH4 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH5 : (tmr_remain_get_entry_facts external critical sg context raw p ty original i before )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  EX (acquired: UCOS2_Verify_State)  (locked: UCOS2_Verify_State)  (current: TimerImage) ,
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ (tmr_remain_get_locked_facts external critical sg context raw p ty original i before acquired locked current ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_remain_get_state (current)))
  **  (tmr_remain_get_payload sg p current locked )
  **  (tmr_remain_get_locked_rest sg raw p ty i current locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
).

Definition OSTmrRemainGet_which_implies_wit_4 := 
(
forall (p: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH3 : ((tmr_remain_get_state (current)) = 3)) ,
  (tmr_remain_get_payload sg p current locked )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_state (current)) = 3) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_remain_get_match (current)))
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> (tmr_remain_get_time (locked)))
) \/
(
forall (p: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH3 : ((tmr_remain_get_state (current)) = 3)) ,
  (tmr_remain_get_payload sg p current locked )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_remain_get_match (current)))
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> (tmr_remain_get_time (locked)))
).

Definition OSTmrRemainGet_which_implies_wit_4_split_goal_spatial := 
forall (p: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : (( &( "OSTmrTime" ) ) = (tmr_remain_get_time_address (sg)))) (PreH3 : ((tmr_remain_get_state (current)) = 3)) ,
  (tmr_remain_get_payload sg p current locked )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_remain_get_match (current)))
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> (tmr_remain_get_time (locked)))
.

Definition OSTmrRemainGet_which_implies_wit_5 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
).

Definition OSTmrRemainGet_which_implies_wit_5_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
.

Definition OSTmrRemainGet_which_implies_wit_5_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
.

Definition OSTmrRemainGet_which_implies_wit_6 := 
(
forall (p: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_state (current)) = 1)) ,
  (tmr_remain_get_payload sg p current locked )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_state (current)) = 1) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
) \/
(
forall (p: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_state (current)) = 1)) ,
  (tmr_remain_get_payload sg p current locked )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
).

Definition OSTmrRemainGet_which_implies_wit_6_split_goal_spatial := 
forall (p: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_state (current)) = 1)) ,
  (tmr_remain_get_payload sg p current locked )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_remain_get_option (current)))
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_remain_get_delay (current)))
  **  (tmr_remain_get_period_storage p current )
.

Definition OSTmrRemainGet_which_implies_wit_7 := 
(
forall (p: Z) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_option (current)) = 2)) (PreH3 : ((tmr_remain_get_delay (current)) = 0)) ,
  (tmr_remain_get_period_storage p current )
|--
  “ (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") ) ” 
  &&  “ ((tmr_remain_get_option (current)) = 2) ” 
  &&  “ ((tmr_remain_get_delay (current)) = 0) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_remain_get_period (current)))
) \/
(
forall (p: Z) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_option (current)) = 2)) (PreH3 : ((tmr_remain_get_delay (current)) = 0)) ,
  (tmr_remain_get_period_storage p current )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_remain_get_period (current)))
).

Definition OSTmrRemainGet_which_implies_wit_7_split_goal_spatial := 
forall (p: Z) (current: TimerImage) (PreH1 : (tmr_remain_get_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") &((p)  # "os_tmr" ->ₛ "OSTmrOpt") &((p)  # "os_tmr" ->ₛ "OSTmrDly") &((p)  # "os_tmr" ->ₛ "OSTmrPeriod") &((p)  # "os_tmr" ->ₛ "OSTmrMatch") )) (PreH2 : ((tmr_remain_get_option (current)) = 2)) (PreH3 : ((tmr_remain_get_delay (current)) = 0)) ,
  (tmr_remain_get_period_storage p current )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_remain_get_period (current)))
.

Definition OSTmrRemainGet_which_implies_wit_8 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
).

Definition OSTmrRemainGet_which_implies_wit_8_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
.

Definition OSTmrRemainGet_which_implies_wit_8_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
.

Definition OSTmrRemainGet_which_implies_wit_9 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
).

Definition OSTmrRemainGet_which_implies_wit_9_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked remain 0 ) ”
.

Definition OSTmrRemainGet_which_implies_wit_9_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) (remain: Z) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current remain 0 )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
.

Definition OSTmrRemainGet_which_implies_wit_10 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
).

Definition OSTmrRemainGet_which_implies_wit_10_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 0 ) ”
.

Definition OSTmrRemainGet_which_implies_wit_10_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 0 )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
.

Definition OSTmrRemainGet_which_implies_wit_11 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
).

Definition OSTmrRemainGet_which_implies_wit_11_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 135 ) ”
.

Definition OSTmrRemainGet_which_implies_wit_11_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 135 )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
.

Definition OSTmrRemainGet_which_implies_wit_12 := 
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
) \/
(
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
).

Definition OSTmrRemainGet_which_implies_wit_12_split_goal_1 := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
|--
  “ (tmr_remain_get_observed critical sg context raw p ty original i before locked 0 141 ) ”
.

Definition OSTmrRemainGet_which_implies_wit_12_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (i: Z) (original: TimerImage) (ty: Z) (p: Z) (raw: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (current: TimerImage) ,
  (tmr_remain_get_ready external platform critical sg context mask raw p ty original i before acquired locked current 0 141 )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_remain_get_private raw p ty (tmr_remain_get_ints (before)) original )
.

Module Type VC_Correct.


Axiom proof_of_OSTmrRemainGet_safety_wit_1 : OSTmrRemainGet_safety_wit_1.
Axiom proof_of_OSTmrRemainGet_entail_wit_1 : OSTmrRemainGet_entail_wit_1.
Axiom proof_of_OSTmrRemainGet_entail_wit_2_1 : OSTmrRemainGet_entail_wit_2_1.
Axiom proof_of_OSTmrRemainGet_entail_wit_2_2 : OSTmrRemainGet_entail_wit_2_2.
Axiom proof_of_OSTmrRemainGet_entail_wit_3_1 : OSTmrRemainGet_entail_wit_3_1.
Axiom proof_of_OSTmrRemainGet_entail_wit_3_2 : OSTmrRemainGet_entail_wit_3_2.
Axiom proof_of_OSTmrRemainGet_entail_wit_4_1 : OSTmrRemainGet_entail_wit_4_1.
Axiom proof_of_OSTmrRemainGet_entail_wit_4_2 : OSTmrRemainGet_entail_wit_4_2.
Axiom proof_of_OSTmrRemainGet_entail_wit_5 : OSTmrRemainGet_entail_wit_5.
Axiom proof_of_OSTmrRemainGet_entail_wit_6 : OSTmrRemainGet_entail_wit_6.
Axiom proof_of_OSTmrRemainGet_entail_wit_7 : OSTmrRemainGet_entail_wit_7.
Axiom proof_of_OSTmrRemainGet_return_wit_1 : OSTmrRemainGet_return_wit_1.
Axiom proof_of_OSTmrRemainGet_return_wit_2 : OSTmrRemainGet_return_wit_2.
Axiom proof_of_OSTmrRemainGet_return_wit_3 : OSTmrRemainGet_return_wit_3.
Axiom proof_of_OSTmrRemainGet_return_wit_4 : OSTmrRemainGet_return_wit_4.
Axiom proof_of_OSTmrRemainGet_return_wit_5 : OSTmrRemainGet_return_wit_5.
Axiom proof_of_OSTmrRemainGet_return_wit_6 : OSTmrRemainGet_return_wit_6.
Axiom proof_of_OSTmrRemainGet_return_wit_7 : OSTmrRemainGet_return_wit_7.
Axiom proof_of_OSTmrRemainGet_return_wit_8 : OSTmrRemainGet_return_wit_8.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_1_pure : OSTmrRemainGet_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_1 : OSTmrRemainGet_partial_solve_wit_1.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_2_pure : OSTmrRemainGet_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_2 : OSTmrRemainGet_partial_solve_wit_2.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_3_pure : OSTmrRemainGet_partial_solve_wit_3_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_3 : OSTmrRemainGet_partial_solve_wit_3.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_4_pure : OSTmrRemainGet_partial_solve_wit_4_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_4 : OSTmrRemainGet_partial_solve_wit_4.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_5_pure : OSTmrRemainGet_partial_solve_wit_5_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_5 : OSTmrRemainGet_partial_solve_wit_5.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_6 : OSTmrRemainGet_partial_solve_wit_6.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_7_pure : OSTmrRemainGet_partial_solve_wit_7_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_7 : OSTmrRemainGet_partial_solve_wit_7.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_8_pure : OSTmrRemainGet_partial_solve_wit_8_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_8 : OSTmrRemainGet_partial_solve_wit_8.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_9_pure : OSTmrRemainGet_partial_solve_wit_9_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_9 : OSTmrRemainGet_partial_solve_wit_9.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_10 : OSTmrRemainGet_partial_solve_wit_10.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_11_pure : OSTmrRemainGet_partial_solve_wit_11_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_11 : OSTmrRemainGet_partial_solve_wit_11.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_12_pure : OSTmrRemainGet_partial_solve_wit_12_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_12 : OSTmrRemainGet_partial_solve_wit_12.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_13 : OSTmrRemainGet_partial_solve_wit_13.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_14 : OSTmrRemainGet_partial_solve_wit_14.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_15_pure : OSTmrRemainGet_partial_solve_wit_15_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_15 : OSTmrRemainGet_partial_solve_wit_15.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_16 : OSTmrRemainGet_partial_solve_wit_16.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_17_pure : OSTmrRemainGet_partial_solve_wit_17_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_17 : OSTmrRemainGet_partial_solve_wit_17.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_18_pure : OSTmrRemainGet_partial_solve_wit_18_pure.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_18 : OSTmrRemainGet_partial_solve_wit_18.
Axiom proof_of_OSTmrRemainGet_partial_solve_wit_19 : OSTmrRemainGet_partial_solve_wit_19.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_1 : OSTmrRemainGet_which_implies_wit_1.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_2 : OSTmrRemainGet_which_implies_wit_2.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_3 : OSTmrRemainGet_which_implies_wit_3.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_4 : OSTmrRemainGet_which_implies_wit_4.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_5 : OSTmrRemainGet_which_implies_wit_5.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_6 : OSTmrRemainGet_which_implies_wit_6.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_7 : OSTmrRemainGet_which_implies_wit_7.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_8 : OSTmrRemainGet_which_implies_wit_8.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_9 : OSTmrRemainGet_which_implies_wit_9.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_10 : OSTmrRemainGet_which_implies_wit_10.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_11 : OSTmrRemainGet_which_implies_wit_11.
Axiom proof_of_OSTmrRemainGet_which_implies_wit_12 : OSTmrRemainGet_which_implies_wit_12.

End VC_Correct.
