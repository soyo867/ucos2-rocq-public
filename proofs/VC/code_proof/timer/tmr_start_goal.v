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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_start_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmrStart -----*)

Definition OSTmrStart_safety_wit_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = p)) (PreH2 : (perr_pre = error_addr)) (PreH3 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH8 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrStart_return_wit_1 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context locked returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (p <> 0)) (PreH13 : (ty = 100)) (PreH14 : ((os_sched_lock_ints (before)) = 0)) (PreH15 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH17 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH19 : ((os_sched_lock_ints (before)) <= 0)) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH23 : (0 <= ty)) (PreH24 : (ty <= 255)) (PreH25 : (0 <= (os_sched_lock_ints (before)))) (PreH26 : ((os_sched_lock_ints (before)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH29 : (p <> 0)) (PreH30 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (ptmr_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (perr_pre = error_addr)) (PreH35 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH36 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH39 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH40 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH41 : (3 <> status)) (PreH42 : (1 <> status)) (PreH43 : (2 <> status)) (PreH44 : (0 <> status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context locked returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (p <> 0)) (PreH13 : (ty = 100)) (PreH14 : ((os_sched_lock_ints (before)) = 0)) (PreH15 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH17 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH19 : ((os_sched_lock_ints (before)) <= 0)) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH23 : (0 <= ty)) (PreH24 : (ty <= 255)) (PreH25 : (0 <= (os_sched_lock_ints (before)))) (PreH26 : ((os_sched_lock_ints (before)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH29 : (p <> 0)) (PreH30 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (ptmr_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (perr_pre = error_addr)) (PreH35 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH36 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH39 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH40 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH41 : (3 <> status)) (PreH42 : (1 <> status)) (PreH43 : (2 <> status)) (PreH44 : (0 <> status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
).

Definition OSTmrStart_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context locked returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (p <> 0)) (PreH13 : (ty = 100)) (PreH14 : ((os_sched_lock_ints (before)) = 0)) (PreH15 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH17 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH19 : ((os_sched_lock_ints (before)) <= 0)) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH23 : (0 <= ty)) (PreH24 : (ty <= 255)) (PreH25 : (0 <= (os_sched_lock_ints (before)))) (PreH26 : ((os_sched_lock_ints (before)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH29 : (p <> 0)) (PreH30 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (ptmr_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (perr_pre = error_addr)) (PreH35 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH36 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH39 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH40 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH41 : (3 <> status)) (PreH42 : (1 <> status)) (PreH43 : (2 <> status)) (PreH44 : (0 <> status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
.

Definition OSTmrStart_return_wit_2 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context locked returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (p <> 0)) (PreH13 : (ty = 100)) (PreH14 : ((os_sched_lock_ints (before)) = 0)) (PreH15 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH17 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH19 : ((os_sched_lock_ints (before)) <= 0)) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH23 : (0 <= ty)) (PreH24 : (ty <= 255)) (PreH25 : (0 <= (os_sched_lock_ints (before)))) (PreH26 : ((os_sched_lock_ints (before)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH29 : (p <> 0)) (PreH30 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (ptmr_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (perr_pre = error_addr)) (PreH35 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH36 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH39 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH40 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH41 : (3 <> status)) (PreH42 : (1 <> status)) (PreH43 : (2 <> status)) (PreH44 : (0 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context locked returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (p <> 0)) (PreH13 : (ty = 100)) (PreH14 : ((os_sched_lock_ints (before)) = 0)) (PreH15 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH17 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH19 : ((os_sched_lock_ints (before)) <= 0)) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH23 : (0 <= ty)) (PreH24 : (ty <= 255)) (PreH25 : (0 <= (os_sched_lock_ints (before)))) (PreH26 : ((os_sched_lock_ints (before)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH29 : (p <> 0)) (PreH30 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (ptmr_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (perr_pre = error_addr)) (PreH35 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH36 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH39 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH40 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH41 : (3 <> status)) (PreH42 : (1 <> status)) (PreH43 : (2 <> status)) (PreH44 : (0 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
).

Definition OSTmrStart_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context locked returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (p <> 0)) (PreH13 : (ty = 100)) (PreH14 : ((os_sched_lock_ints (before)) = 0)) (PreH15 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH17 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH19 : ((os_sched_lock_ints (before)) <= 0)) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH23 : (0 <= ty)) (PreH24 : (ty <= 255)) (PreH25 : (0 <= (os_sched_lock_ints (before)))) (PreH26 : ((os_sched_lock_ints (before)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH29 : (p <> 0)) (PreH30 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (ptmr_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (perr_pre = error_addr)) (PreH35 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH36 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH39 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH40 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH41 : (3 <> status)) (PreH42 : (1 <> status)) (PreH43 : (2 <> status)) (PreH44 : (0 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
.

Definition OSTmrStart_return_wit_3 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_nonrunning_status status )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (pooled = true)) (PreH14 : (p = (timer_pool_addr (sg) (i)))) (PreH15 : (tmr_link_layout )) (PreH16 : (tmr_unlink_layout )) (PreH17 : (tmr_link_profile sg )) (PreH18 : (tmr_unlink_profile sg )) (PreH19 : (UCOS2_state_inv sg locked )) (PreH20 : (timer_api_initialized (TimerState (locked)) )) (PreH21 : (tmr_link_eligible (TimerState (locked)) i )) (PreH22 : (p <> 0)) (PreH23 : (ty = 100)) (PreH24 : ((os_sched_lock_ints (before)) = 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH28 : (p <> 0)) (PreH29 : (ty = 100)) (PreH30 : ((os_sched_lock_ints (before)) = 0)) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH33 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : ((os_sched_lock_ints (before)) <= 0)) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH38 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH39 : (0 <= ty)) (PreH40 : (ty <= 255)) (PreH41 : (0 <= (os_sched_lock_ints (before)))) (PreH42 : ((os_sched_lock_ints (before)) <= 255)) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH45 : (p <> 0)) (PreH46 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH48 : (ptmr_pre <> 0)) (PreH49 : (ptmr_pre = p)) (PreH50 : (perr_pre = error_addr)) (PreH51 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH52 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH53 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH54 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH55 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH56 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH57 : (3 <> status)) (PreH58 : (1 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_nonrunning_status status )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (pooled = true)) (PreH14 : (p = (timer_pool_addr (sg) (i)))) (PreH15 : (tmr_link_layout )) (PreH16 : (tmr_unlink_layout )) (PreH17 : (tmr_link_profile sg )) (PreH18 : (tmr_unlink_profile sg )) (PreH19 : (UCOS2_state_inv sg locked )) (PreH20 : (timer_api_initialized (TimerState (locked)) )) (PreH21 : (tmr_link_eligible (TimerState (locked)) i )) (PreH22 : (p <> 0)) (PreH23 : (ty = 100)) (PreH24 : ((os_sched_lock_ints (before)) = 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH28 : (p <> 0)) (PreH29 : (ty = 100)) (PreH30 : ((os_sched_lock_ints (before)) = 0)) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH33 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : ((os_sched_lock_ints (before)) <= 0)) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH38 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH39 : (0 <= ty)) (PreH40 : (ty <= 255)) (PreH41 : (0 <= (os_sched_lock_ints (before)))) (PreH42 : ((os_sched_lock_ints (before)) <= 255)) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH45 : (p <> 0)) (PreH46 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH48 : (ptmr_pre <> 0)) (PreH49 : (ptmr_pre = p)) (PreH50 : (perr_pre = error_addr)) (PreH51 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH52 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH53 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH54 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH55 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH56 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH57 : (3 <> status)) (PreH58 : (1 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
).

Definition OSTmrStart_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_nonrunning_status status )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (pooled = true)) (PreH14 : (p = (timer_pool_addr (sg) (i)))) (PreH15 : (tmr_link_layout )) (PreH16 : (tmr_unlink_layout )) (PreH17 : (tmr_link_profile sg )) (PreH18 : (tmr_unlink_profile sg )) (PreH19 : (UCOS2_state_inv sg locked )) (PreH20 : (timer_api_initialized (TimerState (locked)) )) (PreH21 : (tmr_link_eligible (TimerState (locked)) i )) (PreH22 : (p <> 0)) (PreH23 : (ty = 100)) (PreH24 : ((os_sched_lock_ints (before)) = 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH28 : (p <> 0)) (PreH29 : (ty = 100)) (PreH30 : ((os_sched_lock_ints (before)) = 0)) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH33 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : ((os_sched_lock_ints (before)) <= 0)) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH38 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH39 : (0 <= ty)) (PreH40 : (ty <= 255)) (PreH41 : (0 <= (os_sched_lock_ints (before)))) (PreH42 : ((os_sched_lock_ints (before)) <= 255)) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH45 : (p <> 0)) (PreH46 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH48 : (ptmr_pre <> 0)) (PreH49 : (ptmr_pre = p)) (PreH50 : (perr_pre = error_addr)) (PreH51 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH52 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH53 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH54 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH55 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH56 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH57 : (3 <> status)) (PreH58 : (1 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
.

Definition OSTmrStart_return_wit_4 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_nonrunning_status status )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (pooled = true)) (PreH14 : (p = (timer_pool_addr (sg) (i)))) (PreH15 : (tmr_link_layout )) (PreH16 : (tmr_unlink_layout )) (PreH17 : (tmr_link_profile sg )) (PreH18 : (tmr_unlink_profile sg )) (PreH19 : (UCOS2_state_inv sg locked )) (PreH20 : (timer_api_initialized (TimerState (locked)) )) (PreH21 : (tmr_link_eligible (TimerState (locked)) i )) (PreH22 : (p <> 0)) (PreH23 : (ty = 100)) (PreH24 : ((os_sched_lock_ints (before)) = 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH28 : (p <> 0)) (PreH29 : (ty = 100)) (PreH30 : ((os_sched_lock_ints (before)) = 0)) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH33 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : ((os_sched_lock_ints (before)) <= 0)) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH38 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH39 : (0 <= ty)) (PreH40 : (ty <= 255)) (PreH41 : (0 <= (os_sched_lock_ints (before)))) (PreH42 : ((os_sched_lock_ints (before)) <= 255)) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH45 : (p <> 0)) (PreH46 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH48 : (ptmr_pre <> 0)) (PreH49 : (ptmr_pre = p)) (PreH50 : (perr_pre = error_addr)) (PreH51 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH52 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH53 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH54 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH55 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH56 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH57 : (3 <> status)) (PreH58 : (1 <> status)) (PreH59 : (2 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_nonrunning_status status )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (pooled = true)) (PreH14 : (p = (timer_pool_addr (sg) (i)))) (PreH15 : (tmr_link_layout )) (PreH16 : (tmr_unlink_layout )) (PreH17 : (tmr_link_profile sg )) (PreH18 : (tmr_unlink_profile sg )) (PreH19 : (UCOS2_state_inv sg locked )) (PreH20 : (timer_api_initialized (TimerState (locked)) )) (PreH21 : (tmr_link_eligible (TimerState (locked)) i )) (PreH22 : (p <> 0)) (PreH23 : (ty = 100)) (PreH24 : ((os_sched_lock_ints (before)) = 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH28 : (p <> 0)) (PreH29 : (ty = 100)) (PreH30 : ((os_sched_lock_ints (before)) = 0)) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH33 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : ((os_sched_lock_ints (before)) <= 0)) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH38 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH39 : (0 <= ty)) (PreH40 : (ty <= 255)) (PreH41 : (0 <= (os_sched_lock_ints (before)))) (PreH42 : ((os_sched_lock_ints (before)) <= 255)) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH45 : (p <> 0)) (PreH46 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH48 : (ptmr_pre <> 0)) (PreH49 : (ptmr_pre = p)) (PreH50 : (perr_pre = error_addr)) (PreH51 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH52 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH53 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH54 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH55 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH56 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH57 : (3 <> status)) (PreH58 : (1 <> status)) (PreH59 : (2 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
).

Definition OSTmrStart_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (p <> 0)) (PreH7 : (ty = 100)) (PreH8 : ((os_sched_lock_ints (before)) = 0)) (PreH9 : (tmr_start_nonrunning_status status )) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (pooled = true)) (PreH14 : (p = (timer_pool_addr (sg) (i)))) (PreH15 : (tmr_link_layout )) (PreH16 : (tmr_unlink_layout )) (PreH17 : (tmr_link_profile sg )) (PreH18 : (tmr_unlink_profile sg )) (PreH19 : (UCOS2_state_inv sg locked )) (PreH20 : (timer_api_initialized (TimerState (locked)) )) (PreH21 : (tmr_link_eligible (TimerState (locked)) i )) (PreH22 : (p <> 0)) (PreH23 : (ty = 100)) (PreH24 : ((os_sched_lock_ints (before)) = 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH28 : (p <> 0)) (PreH29 : (ty = 100)) (PreH30 : ((os_sched_lock_ints (before)) = 0)) (PreH31 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH32 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH33 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : ((os_sched_lock_ints (before)) <= 0)) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH38 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH39 : (0 <= ty)) (PreH40 : (ty <= 255)) (PreH41 : (0 <= (os_sched_lock_ints (before)))) (PreH42 : ((os_sched_lock_ints (before)) <= 255)) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH45 : (p <> 0)) (PreH46 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH48 : (ptmr_pre <> 0)) (PreH49 : (ptmr_pre = p)) (PreH50 : (perr_pre = error_addr)) (PreH51 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH52 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH53 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH54 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH55 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH56 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH57 : (3 <> status)) (PreH58 : (1 <> status)) (PreH59 : (2 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
.

Definition OSTmrStart_return_wit_5 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH7 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH8 : (timer_api_initialized stopped )) (PreH9 : (tmr_link_eligible stopped i )) (PreH10 : (p <> 0)) (PreH11 : (ty = 100)) (PreH12 : ((os_sched_lock_ints (before)) = 0)) (PreH13 : (status = 3)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (pooled = true)) (PreH18 : (p = (timer_pool_addr (sg) (i)))) (PreH19 : (tmr_link_layout )) (PreH20 : (tmr_unlink_layout )) (PreH21 : (tmr_link_profile sg )) (PreH22 : (tmr_unlink_profile sg )) (PreH23 : (UCOS2_state_inv sg locked )) (PreH24 : (timer_api_initialized (TimerState (locked)) )) (PreH25 : (tmr_unlink_running (TimerState (locked)) i )) (PreH26 : (p <> 0)) (PreH27 : (ty = 100)) (PreH28 : ((os_sched_lock_ints (before)) = 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH32 : (p <> 0)) (PreH33 : (ty = 100)) (PreH34 : ((os_sched_lock_ints (before)) = 0)) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH37 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH38 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH39 : ((os_sched_lock_ints (before)) <= 0)) (PreH40 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (0 <= ty)) (PreH44 : (ty <= 255)) (PreH45 : (0 <= (os_sched_lock_ints (before)))) (PreH46 : ((os_sched_lock_ints (before)) <= 255)) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH49 : (p <> 0)) (PreH50 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (ptmr_pre <> 0)) (PreH53 : (ptmr_pre = p)) (PreH54 : (perr_pre = error_addr)) (PreH55 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH56 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH57 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH58 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH59 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH60 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH61 : (3 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH7 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH8 : (timer_api_initialized stopped )) (PreH9 : (tmr_link_eligible stopped i )) (PreH10 : (p <> 0)) (PreH11 : (ty = 100)) (PreH12 : ((os_sched_lock_ints (before)) = 0)) (PreH13 : (status = 3)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (pooled = true)) (PreH18 : (p = (timer_pool_addr (sg) (i)))) (PreH19 : (tmr_link_layout )) (PreH20 : (tmr_unlink_layout )) (PreH21 : (tmr_link_profile sg )) (PreH22 : (tmr_unlink_profile sg )) (PreH23 : (UCOS2_state_inv sg locked )) (PreH24 : (timer_api_initialized (TimerState (locked)) )) (PreH25 : (tmr_unlink_running (TimerState (locked)) i )) (PreH26 : (p <> 0)) (PreH27 : (ty = 100)) (PreH28 : ((os_sched_lock_ints (before)) = 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH32 : (p <> 0)) (PreH33 : (ty = 100)) (PreH34 : ((os_sched_lock_ints (before)) = 0)) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH37 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH38 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH39 : ((os_sched_lock_ints (before)) <= 0)) (PreH40 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (0 <= ty)) (PreH44 : (ty <= 255)) (PreH45 : (0 <= (os_sched_lock_ints (before)))) (PreH46 : ((os_sched_lock_ints (before)) <= 255)) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH49 : (p <> 0)) (PreH50 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (ptmr_pre <> 0)) (PreH53 : (ptmr_pre = p)) (PreH54 : (perr_pre = error_addr)) (PreH55 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH56 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH57 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH58 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH59 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH60 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH61 : (3 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
).

Definition OSTmrStart_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (PreH1 : (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final )) (PreH2 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH3 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH6 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH7 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH8 : (timer_api_initialized stopped )) (PreH9 : (tmr_link_eligible stopped i )) (PreH10 : (p <> 0)) (PreH11 : (ty = 100)) (PreH12 : ((os_sched_lock_ints (before)) = 0)) (PreH13 : (status = 3)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (pooled = true)) (PreH18 : (p = (timer_pool_addr (sg) (i)))) (PreH19 : (tmr_link_layout )) (PreH20 : (tmr_unlink_layout )) (PreH21 : (tmr_link_profile sg )) (PreH22 : (tmr_unlink_profile sg )) (PreH23 : (UCOS2_state_inv sg locked )) (PreH24 : (timer_api_initialized (TimerState (locked)) )) (PreH25 : (tmr_unlink_running (TimerState (locked)) i )) (PreH26 : (p <> 0)) (PreH27 : (ty = 100)) (PreH28 : ((os_sched_lock_ints (before)) = 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH32 : (p <> 0)) (PreH33 : (ty = 100)) (PreH34 : ((os_sched_lock_ints (before)) = 0)) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH37 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH38 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH39 : ((os_sched_lock_ints (before)) <= 0)) (PreH40 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (0 <= ty)) (PreH44 : (ty <= 255)) (PreH45 : (0 <= (os_sched_lock_ints (before)))) (PreH46 : ((os_sched_lock_ints (before)) <= 255)) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH49 : (p <> 0)) (PreH50 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (ptmr_pre <> 0)) (PreH53 : (ptmr_pre = p)) (PreH54 : (perr_pre = error_addr)) (PreH55 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH56 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH57 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH58 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH59 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH60 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH61 : (3 = status)) ,
  (tmr_start_return_resources external platform critical sg context returned mask final )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 1 before X )
.

Definition OSTmrStart_return_wit_6 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) > 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 139)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) > 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 139)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
).

Definition OSTmrStart_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) > 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 139)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
.

Definition OSTmrStart_return_wit_7 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : ((unsigned_last_nbits (ty) (32)) <> 100)) (PreH3 : (p <> 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (ptmr_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH12 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH13 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : ((unsigned_last_nbits (ty) (32)) <> 100)) (PreH3 : (p <> 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (ptmr_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH12 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH13 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
).

Definition OSTmrStart_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : ((unsigned_last_nbits (ty) (32)) <> 100)) (PreH3 : (p <> 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (ptmr_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH10 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH12 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH13 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
.

Definition OSTmrStart_return_wit_8 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH7 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH8 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 138)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH7 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH8 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 138)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
).

Definition OSTmrStart_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH7 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH8 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |-> 138)
|--
  (tmr_start_post external platform critical sg context mask pooled p i ty raw_state error_addr 0 before X )
.

Definition OSTmrStart_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH7 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH8 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
.

Definition OSTmrStart_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH7 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH8 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_1 := OSTmrStart_partial_solve_wit_1_pure -> OSTmrStart_partial_solve_wit_1_aux.

Definition OSTmrStart_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits (ty) (32)) <> 100)) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (ptmr_pre <> 0)) (PreH6 : (ptmr_pre = p)) (PreH7 : (perr_pre = error_addr)) (PreH8 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH11 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH12 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
.

Definition OSTmrStart_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits (ty) (32)) <> 100)) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (ptmr_pre <> 0)) (PreH6 : (ptmr_pre = p)) (PreH7 : (perr_pre = error_addr)) (PreH8 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH11 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH12 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) <> 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_2 := OSTmrStart_partial_solve_wit_2_pure -> OSTmrStart_partial_solve_wit_2_aux.

Definition OSTmrStart_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (ptmr_pre <> 0)) (PreH6 : (ptmr_pre = p)) (PreH7 : (perr_pre = error_addr)) (PreH8 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH11 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH12 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
.

Definition OSTmrStart_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (ptmr_pre <> 0)) (PreH6 : (ptmr_pre = p)) (PreH7 : (perr_pre = error_addr)) (PreH8 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH11 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH12 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_3 := OSTmrStart_partial_solve_wit_3_pure -> OSTmrStart_partial_solve_wit_3_aux.

Definition OSTmrStart_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_lock_ints (before)) > 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (0 <= ty)) (PreH6 : (ty <= 255)) (PreH7 : (0 <= (os_sched_lock_ints (before)))) (PreH8 : ((os_sched_lock_ints (before)) <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH18 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH21 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTmrStart_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_lock_ints (before)) > 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (0 <= ty)) (PreH6 : (ty <= 255)) (PreH7 : (0 <= (os_sched_lock_ints (before)))) (PreH8 : ((os_sched_lock_ints (before)) <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH18 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH21 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((os_sched_lock_ints (before)) > 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_4 := OSTmrStart_partial_solve_wit_4_pure -> OSTmrStart_partial_solve_wit_4_aux.

Definition OSTmrStart_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_lock_ints (before)) <= 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (0 <= ty)) (PreH6 : (ty <= 255)) (PreH7 : (0 <= (os_sched_lock_ints (before)))) (PreH8 : ((os_sched_lock_ints (before)) <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH18 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH21 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTmrStart_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_lock_ints (before)) <= 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (0 <= ty)) (PreH6 : (ty <= 255)) (PreH7 : (0 <= (os_sched_lock_ints (before)))) (PreH8 : ((os_sched_lock_ints (before)) <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH18 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH21 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH22 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_5 := OSTmrStart_partial_solve_wit_5_pure -> OSTmrStart_partial_solve_wit_5_aux.

Definition OSTmrStart_partial_solve_wit_6_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
).

Definition OSTmrStart_partial_solve_wit_6_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrStart_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_6 := OSTmrStart_partial_solve_wit_6_pure -> OSTmrStart_partial_solve_wit_6_aux.

Definition OSTmrStart_partial_solve_wit_7_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ty = 100) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (ty = 100) ”
).

Definition OSTmrStart_partial_solve_wit_7_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (ty = 100) ”
.

Definition OSTmrStart_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_lock_ints (before)) <= 0)) (PreH3 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (0 <= ty)) (PreH7 : (ty <= 255)) (PreH8 : (0 <= (os_sched_lock_ints (before)))) (PreH9 : ((os_sched_lock_ints (before)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH12 : (p <> 0)) (PreH13 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH22 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ty = 100) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_7 := OSTmrStart_partial_solve_wit_7_pure -> OSTmrStart_partial_solve_wit_7_aux.

Definition OSTmrStart_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH8 : ((os_sched_lock_ints (before)) <= 0)) (PreH9 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH10 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH11 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH12 : (0 <= ty)) (PreH13 : (ty <= 255)) (PreH14 : (0 <= (os_sched_lock_ints (before)))) (PreH15 : ((os_sched_lock_ints (before)) <= 255)) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH18 : (p <> 0)) (PreH19 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH20 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (ptmr_pre = p)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH27 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH28 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH29 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
.

Definition OSTmrStart_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH8 : ((os_sched_lock_ints (before)) <= 0)) (PreH9 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH10 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH11 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH12 : (0 <= ty)) (PreH13 : (ty <= 255)) (PreH14 : (0 <= (os_sched_lock_ints (before)))) (PreH15 : ((os_sched_lock_ints (before)) <= 255)) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH18 : (p <> 0)) (PreH19 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH20 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (ptmr_pre = p)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH27 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH28 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH29 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_8 := OSTmrStart_partial_solve_wit_8_pure -> OSTmrStart_partial_solve_wit_8_aux.

Definition OSTmrStart_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
.

Definition OSTmrStart_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 = status)) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_9 := OSTmrStart_partial_solve_wit_9_pure -> OSTmrStart_partial_solve_wit_9_aux.

Definition OSTmrStart_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_unlink_running (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ”
.

Definition OSTmrStart_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_unlink_running (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 = status)) ,
  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_10 := OSTmrStart_partial_solve_wit_10_pure -> OSTmrStart_partial_solve_wit_10_aux.

Definition OSTmrStart_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_unlink_running (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 = status)) ,
  (tmr_unlink_configured_post sg (TimerState (locked)) i )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ”
.

Definition OSTmrStart_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_unlink_running (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 = status)) ,
  (tmr_unlink_configured_post sg (TimerState (locked)) i )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (tmr_unlink_configured_post sg (TimerState (locked)) i )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_11 := OSTmrStart_partial_solve_wit_11_pure -> OSTmrStart_partial_solve_wit_11_aux.

Definition OSTmrStart_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (PreH1 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH2 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH3 : (timer_api_initialized stopped )) (PreH4 : (tmr_link_eligible stopped i )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (status = 3)) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_unlink_running (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (timer_inv sg stopped )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ”
.

Definition OSTmrStart_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (PreH1 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH2 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH3 : (timer_api_initialized stopped )) (PreH4 : (tmr_link_eligible stopped i )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (status = 3)) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_unlink_running (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 = status)) ,
  (timer_inv sg stopped )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (timer_inv sg stopped )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_12 := OSTmrStart_partial_solve_wit_12_pure -> OSTmrStart_partial_solve_wit_12_aux.

Definition OSTmrStart_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (PreH1 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH2 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH3 : (timer_api_initialized stopped )) (PreH4 : (tmr_link_eligible stopped i )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (status = 3)) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_unlink_running (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 = status)) ,
  (tmr_link_configured_post sg stopped i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ”
.

Definition OSTmrStart_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (PreH1 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH2 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH3 : (timer_api_initialized stopped )) (PreH4 : (tmr_link_eligible stopped i )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (status = 3)) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_unlink_running (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 = status)) ,
  (tmr_link_configured_post sg stopped i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (tmr_link_configured_post sg stopped i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_13 := OSTmrStart_partial_solve_wit_13_pure -> OSTmrStart_partial_solve_wit_13_aux.

Definition OSTmrStart_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH4 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH5 : (timer_api_initialized stopped )) (PreH6 : (tmr_link_eligible stopped i )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (status = 3)) (PreH11 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH12 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH13 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH14 : (pooled = true)) (PreH15 : (p = (timer_pool_addr (sg) (i)))) (PreH16 : (tmr_link_layout )) (PreH17 : (tmr_unlink_layout )) (PreH18 : (tmr_link_profile sg )) (PreH19 : (tmr_unlink_profile sg )) (PreH20 : (UCOS2_state_inv sg locked )) (PreH21 : (timer_api_initialized (TimerState (locked)) )) (PreH22 : (tmr_unlink_running (TimerState (locked)) i )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH27 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (p <> 0)) (PreH30 : (ty = 100)) (PreH31 : ((os_sched_lock_ints (before)) = 0)) (PreH32 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH33 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH34 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : ((os_sched_lock_ints (before)) <= 0)) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (0 <= ty)) (PreH41 : (ty <= 255)) (PreH42 : (0 <= (os_sched_lock_ints (before)))) (PreH43 : ((os_sched_lock_ints (before)) <= 255)) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH46 : (p <> 0)) (PreH47 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH48 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH49 : (ptmr_pre <> 0)) (PreH50 : (ptmr_pre = p)) (PreH51 : (perr_pre = error_addr)) (PreH52 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH53 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH54 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH55 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH56 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH57 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH58 : (3 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
.

Definition OSTmrStart_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH4 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH5 : (timer_api_initialized stopped )) (PreH6 : (tmr_link_eligible stopped i )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (status = 3)) (PreH11 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH12 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH13 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH14 : (pooled = true)) (PreH15 : (p = (timer_pool_addr (sg) (i)))) (PreH16 : (tmr_link_layout )) (PreH17 : (tmr_unlink_layout )) (PreH18 : (tmr_link_profile sg )) (PreH19 : (tmr_unlink_profile sg )) (PreH20 : (UCOS2_state_inv sg locked )) (PreH21 : (timer_api_initialized (TimerState (locked)) )) (PreH22 : (tmr_unlink_running (TimerState (locked)) i )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH27 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (p <> 0)) (PreH30 : (ty = 100)) (PreH31 : ((os_sched_lock_ints (before)) = 0)) (PreH32 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH33 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH34 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : ((os_sched_lock_ints (before)) <= 0)) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (0 <= ty)) (PreH41 : (ty <= 255)) (PreH42 : (0 <= (os_sched_lock_ints (before)))) (PreH43 : ((os_sched_lock_ints (before)) <= 255)) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH46 : (p <> 0)) (PreH47 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH48 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH49 : (ptmr_pre <> 0)) (PreH50 : (ptmr_pre = p)) (PreH51 : (perr_pre = error_addr)) (PreH52 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH53 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH54 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH55 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH56 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH57 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH58 : (3 = status)) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_14 := OSTmrStart_partial_solve_wit_14_pure -> OSTmrStart_partial_solve_wit_14_aux.

Definition OSTmrStart_partial_solve_wit_15_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH6 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH7 : (timer_api_initialized stopped )) (PreH8 : (tmr_link_eligible stopped i )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (status = 3)) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH15 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH16 : (pooled = true)) (PreH17 : (p = (timer_pool_addr (sg) (i)))) (PreH18 : (tmr_link_layout )) (PreH19 : (tmr_unlink_layout )) (PreH20 : (tmr_link_profile sg )) (PreH21 : (tmr_unlink_profile sg )) (PreH22 : (UCOS2_state_inv sg locked )) (PreH23 : (timer_api_initialized (TimerState (locked)) )) (PreH24 : (tmr_unlink_running (TimerState (locked)) i )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH29 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (p <> 0)) (PreH32 : (ty = 100)) (PreH33 : ((os_sched_lock_ints (before)) = 0)) (PreH34 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH35 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH36 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : ((os_sched_lock_ints (before)) <= 0)) (PreH39 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH40 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH41 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH42 : (0 <= ty)) (PreH43 : (ty <= 255)) (PreH44 : (0 <= (os_sched_lock_ints (before)))) (PreH45 : ((os_sched_lock_ints (before)) <= 255)) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH48 : (p <> 0)) (PreH49 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH50 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH51 : (ptmr_pre <> 0)) (PreH52 : (ptmr_pre = p)) (PreH53 : (perr_pre = error_addr)) (PreH54 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH55 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH56 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH57 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH58 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH59 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH60 : (3 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrStart_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH6 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH7 : (timer_api_initialized stopped )) (PreH8 : (tmr_link_eligible stopped i )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (status = 3)) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH15 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH16 : (pooled = true)) (PreH17 : (p = (timer_pool_addr (sg) (i)))) (PreH18 : (tmr_link_layout )) (PreH19 : (tmr_unlink_layout )) (PreH20 : (tmr_link_profile sg )) (PreH21 : (tmr_unlink_profile sg )) (PreH22 : (UCOS2_state_inv sg locked )) (PreH23 : (timer_api_initialized (TimerState (locked)) )) (PreH24 : (tmr_unlink_running (TimerState (locked)) i )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH29 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (p <> 0)) (PreH32 : (ty = 100)) (PreH33 : ((os_sched_lock_ints (before)) = 0)) (PreH34 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH35 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH36 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : ((os_sched_lock_ints (before)) <= 0)) (PreH39 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH40 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH41 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH42 : (0 <= ty)) (PreH43 : (ty <= 255)) (PreH44 : (0 <= (os_sched_lock_ints (before)))) (PreH45 : ((os_sched_lock_ints (before)) <= 255)) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH48 : (p <> 0)) (PreH49 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH50 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH51 : (ptmr_pre <> 0)) (PreH52 : (ptmr_pre = p)) (PreH53 : (perr_pre = error_addr)) (PreH54 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH55 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH56 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH57 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH58 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH59 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH60 : (3 = status)) ,
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_15 := OSTmrStart_partial_solve_wit_15_pure -> OSTmrStart_partial_solve_wit_15_aux.

Definition OSTmrStart_partial_solve_wit_16 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH6 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH7 : (timer_api_initialized stopped )) (PreH8 : (tmr_link_eligible stopped i )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (status = 3)) (PreH13 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH14 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH15 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH16 : (pooled = true)) (PreH17 : (p = (timer_pool_addr (sg) (i)))) (PreH18 : (tmr_link_layout )) (PreH19 : (tmr_unlink_layout )) (PreH20 : (tmr_link_profile sg )) (PreH21 : (tmr_unlink_profile sg )) (PreH22 : (UCOS2_state_inv sg locked )) (PreH23 : (timer_api_initialized (TimerState (locked)) )) (PreH24 : (tmr_unlink_running (TimerState (locked)) i )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH29 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (p <> 0)) (PreH32 : (ty = 100)) (PreH33 : ((os_sched_lock_ints (before)) = 0)) (PreH34 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH35 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH36 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH37 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH38 : ((os_sched_lock_ints (before)) <= 0)) (PreH39 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH40 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH41 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH42 : (0 <= ty)) (PreH43 : (ty <= 255)) (PreH44 : (0 <= (os_sched_lock_ints (before)))) (PreH45 : ((os_sched_lock_ints (before)) <= 255)) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH48 : (p <> 0)) (PreH49 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH50 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH51 : (ptmr_pre <> 0)) (PreH52 : (ptmr_pre = p)) (PreH53 : (perr_pre = error_addr)) (PreH54 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH55 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH56 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH57 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH58 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH59 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH60 : (3 = status)) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 = status) ”
  &&  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_17_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (tmr_start_nonrunning_status 2 ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_nonrunning_status 2 ) ” 
  &&  “ (tmr_start_nonrunning_status 2 ) ”
).

Definition OSTmrStart_partial_solve_wit_17_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_nonrunning_status 2 ) ”
.

Definition OSTmrStart_partial_solve_wit_17_pure_split_goal_2 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_nonrunning_status 2 ) ”
.

Definition OSTmrStart_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 = status)) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (tmr_start_nonrunning_status 2 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 = status) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_17 := OSTmrStart_partial_solve_wit_17_pure -> OSTmrStart_partial_solve_wit_17_aux.

Definition OSTmrStart_partial_solve_wit_18_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (tmr_start_nonrunning_status 1 ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_nonrunning_status 1 ) ” 
  &&  “ (tmr_start_nonrunning_status 1 ) ”
).

Definition OSTmrStart_partial_solve_wit_18_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_nonrunning_status 1 ) ”
.

Definition OSTmrStart_partial_solve_wit_18_pure_split_goal_2 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_nonrunning_status 1 ) ”
.

Definition OSTmrStart_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 = status)) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (tmr_start_nonrunning_status 1 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 = status) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_18 := OSTmrStart_partial_solve_wit_18_pure -> OSTmrStart_partial_solve_wit_18_aux.

Definition OSTmrStart_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ”
.

Definition OSTmrStart_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 = status)) ,
  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 = status) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_19 := OSTmrStart_partial_solve_wit_19_pure -> OSTmrStart_partial_solve_wit_19_aux.

Definition OSTmrStart_partial_solve_wit_20_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 <> status)) (PreH54 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ”
.

Definition OSTmrStart_partial_solve_wit_20_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 <> status)) (PreH54 : (2 = status)) ,
  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 = status) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_20 := OSTmrStart_partial_solve_wit_20_pure -> OSTmrStart_partial_solve_wit_20_aux.

Definition OSTmrStart_partial_solve_wit_21_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 <> status)) (PreH54 : (2 = status)) ,
  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ”
.

Definition OSTmrStart_partial_solve_wit_21_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 <> status)) (PreH54 : (2 = status)) ,
  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 = status) ”
  &&  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_21 := OSTmrStart_partial_solve_wit_21_pure -> OSTmrStart_partial_solve_wit_21_aux.

Definition OSTmrStart_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 = status)) ,
  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ”
.

Definition OSTmrStart_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH7 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH8 : (pooled = true)) (PreH9 : (p = (timer_pool_addr (sg) (i)))) (PreH10 : (tmr_link_layout )) (PreH11 : (tmr_unlink_layout )) (PreH12 : (tmr_link_profile sg )) (PreH13 : (tmr_unlink_profile sg )) (PreH14 : (UCOS2_state_inv sg locked )) (PreH15 : (timer_api_initialized (TimerState (locked)) )) (PreH16 : (tmr_link_eligible (TimerState (locked)) i )) (PreH17 : (p <> 0)) (PreH18 : (ty = 100)) (PreH19 : ((os_sched_lock_ints (before)) = 0)) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH23 : (p <> 0)) (PreH24 : (ty = 100)) (PreH25 : ((os_sched_lock_ints (before)) = 0)) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH28 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH29 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH30 : ((os_sched_lock_ints (before)) <= 0)) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH34 : (0 <= ty)) (PreH35 : (ty <= 255)) (PreH36 : (0 <= (os_sched_lock_ints (before)))) (PreH37 : ((os_sched_lock_ints (before)) <= 255)) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH40 : (p <> 0)) (PreH41 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH42 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH43 : (ptmr_pre <> 0)) (PreH44 : (ptmr_pre = p)) (PreH45 : (perr_pre = error_addr)) (PreH46 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH47 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH48 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH49 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH50 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH51 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH52 : (3 <> status)) (PreH53 : (1 = status)) ,
  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 = status) ”
  &&  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_22 := OSTmrStart_partial_solve_wit_22_pure -> OSTmrStart_partial_solve_wit_22_aux.

Definition OSTmrStart_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_nonrunning_status status )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH9 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH10 : (pooled = true)) (PreH11 : (p = (timer_pool_addr (sg) (i)))) (PreH12 : (tmr_link_layout )) (PreH13 : (tmr_unlink_layout )) (PreH14 : (tmr_link_profile sg )) (PreH15 : (tmr_unlink_profile sg )) (PreH16 : (UCOS2_state_inv sg locked )) (PreH17 : (timer_api_initialized (TimerState (locked)) )) (PreH18 : (tmr_link_eligible (TimerState (locked)) i )) (PreH19 : (p <> 0)) (PreH20 : (ty = 100)) (PreH21 : ((os_sched_lock_ints (before)) = 0)) (PreH22 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH24 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : ((os_sched_lock_ints (before)) <= 0)) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (0 <= ty)) (PreH37 : (ty <= 255)) (PreH38 : (0 <= (os_sched_lock_ints (before)))) (PreH39 : ((os_sched_lock_ints (before)) <= 255)) (PreH40 : (UCOS2_state_inv sg before )) (PreH41 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH42 : (p <> 0)) (PreH43 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH44 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH45 : (ptmr_pre <> 0)) (PreH46 : (ptmr_pre = p)) (PreH47 : (perr_pre = error_addr)) (PreH48 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH49 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH50 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH51 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH52 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH53 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH54 : (3 <> status)) (PreH55 : (1 <> status)) (PreH56 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
.

Definition OSTmrStart_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_nonrunning_status status )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH9 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH10 : (pooled = true)) (PreH11 : (p = (timer_pool_addr (sg) (i)))) (PreH12 : (tmr_link_layout )) (PreH13 : (tmr_unlink_layout )) (PreH14 : (tmr_link_profile sg )) (PreH15 : (tmr_unlink_profile sg )) (PreH16 : (UCOS2_state_inv sg locked )) (PreH17 : (timer_api_initialized (TimerState (locked)) )) (PreH18 : (tmr_link_eligible (TimerState (locked)) i )) (PreH19 : (p <> 0)) (PreH20 : (ty = 100)) (PreH21 : ((os_sched_lock_ints (before)) = 0)) (PreH22 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH24 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : ((os_sched_lock_ints (before)) <= 0)) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (0 <= ty)) (PreH37 : (ty <= 255)) (PreH38 : (0 <= (os_sched_lock_ints (before)))) (PreH39 : ((os_sched_lock_ints (before)) <= 255)) (PreH40 : (UCOS2_state_inv sg before )) (PreH41 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH42 : (p <> 0)) (PreH43 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH44 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH45 : (ptmr_pre <> 0)) (PreH46 : (ptmr_pre = p)) (PreH47 : (perr_pre = error_addr)) (PreH48 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH49 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH50 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH51 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH52 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH53 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH54 : (3 <> status)) (PreH55 : (1 <> status)) (PreH56 : (2 = status)) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 = status) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_23 := OSTmrStart_partial_solve_wit_23_pure -> OSTmrStart_partial_solve_wit_23_aux.

Definition OSTmrStart_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_nonrunning_status status )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH9 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH10 : (pooled = true)) (PreH11 : (p = (timer_pool_addr (sg) (i)))) (PreH12 : (tmr_link_layout )) (PreH13 : (tmr_unlink_layout )) (PreH14 : (tmr_link_profile sg )) (PreH15 : (tmr_unlink_profile sg )) (PreH16 : (UCOS2_state_inv sg locked )) (PreH17 : (timer_api_initialized (TimerState (locked)) )) (PreH18 : (tmr_link_eligible (TimerState (locked)) i )) (PreH19 : (p <> 0)) (PreH20 : (ty = 100)) (PreH21 : ((os_sched_lock_ints (before)) = 0)) (PreH22 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH24 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : ((os_sched_lock_ints (before)) <= 0)) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (0 <= ty)) (PreH37 : (ty <= 255)) (PreH38 : (0 <= (os_sched_lock_ints (before)))) (PreH39 : ((os_sched_lock_ints (before)) <= 255)) (PreH40 : (UCOS2_state_inv sg before )) (PreH41 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH42 : (p <> 0)) (PreH43 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH44 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH45 : (ptmr_pre <> 0)) (PreH46 : (ptmr_pre = p)) (PreH47 : (perr_pre = error_addr)) (PreH48 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH49 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH50 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH51 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH52 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH53 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH54 : (3 <> status)) (PreH55 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
.

Definition OSTmrStart_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_nonrunning_status status )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH9 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH10 : (pooled = true)) (PreH11 : (p = (timer_pool_addr (sg) (i)))) (PreH12 : (tmr_link_layout )) (PreH13 : (tmr_unlink_layout )) (PreH14 : (tmr_link_profile sg )) (PreH15 : (tmr_unlink_profile sg )) (PreH16 : (UCOS2_state_inv sg locked )) (PreH17 : (timer_api_initialized (TimerState (locked)) )) (PreH18 : (tmr_link_eligible (TimerState (locked)) i )) (PreH19 : (p <> 0)) (PreH20 : (ty = 100)) (PreH21 : ((os_sched_lock_ints (before)) = 0)) (PreH22 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH23 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH24 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH25 : (p <> 0)) (PreH26 : (ty = 100)) (PreH27 : ((os_sched_lock_ints (before)) = 0)) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH30 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH32 : ((os_sched_lock_ints (before)) <= 0)) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (0 <= ty)) (PreH37 : (ty <= 255)) (PreH38 : (0 <= (os_sched_lock_ints (before)))) (PreH39 : ((os_sched_lock_ints (before)) <= 255)) (PreH40 : (UCOS2_state_inv sg before )) (PreH41 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH42 : (p <> 0)) (PreH43 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH44 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH45 : (ptmr_pre <> 0)) (PreH46 : (ptmr_pre = p)) (PreH47 : (perr_pre = error_addr)) (PreH48 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH49 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH50 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH51 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH52 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH53 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH54 : (3 <> status)) (PreH55 : (1 = status)) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 = status) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_24 := OSTmrStart_partial_solve_wit_24_pure -> OSTmrStart_partial_solve_wit_24_aux.

Definition OSTmrStart_partial_solve_wit_25_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_link_eligible (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 <> status)) (PreH57 : (1 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrStart_partial_solve_wit_25_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_link_eligible (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 <> status)) (PreH57 : (1 = status)) ,
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 = status) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_25 := OSTmrStart_partial_solve_wit_25_pure -> OSTmrStart_partial_solve_wit_25_aux.

Definition OSTmrStart_partial_solve_wit_26_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_link_eligible (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 <> status)) (PreH57 : (1 <> status)) (PreH58 : (2 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrStart_partial_solve_wit_26_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_link_eligible (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 <> status)) (PreH57 : (1 <> status)) (PreH58 : (2 = status)) ,
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 = status) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_26 := OSTmrStart_partial_solve_wit_26_pure -> OSTmrStart_partial_solve_wit_26_aux.

Definition OSTmrStart_partial_solve_wit_27 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_link_eligible (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 <> status)) (PreH57 : (1 <> status)) (PreH58 : (2 = status)) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 = status) ”
  &&  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_28 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH12 : (pooled = true)) (PreH13 : (p = (timer_pool_addr (sg) (i)))) (PreH14 : (tmr_link_layout )) (PreH15 : (tmr_unlink_layout )) (PreH16 : (tmr_link_profile sg )) (PreH17 : (tmr_unlink_profile sg )) (PreH18 : (UCOS2_state_inv sg locked )) (PreH19 : (timer_api_initialized (TimerState (locked)) )) (PreH20 : (tmr_link_eligible (TimerState (locked)) i )) (PreH21 : (p <> 0)) (PreH22 : (ty = 100)) (PreH23 : ((os_sched_lock_ints (before)) = 0)) (PreH24 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH25 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH26 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH27 : (p <> 0)) (PreH28 : (ty = 100)) (PreH29 : ((os_sched_lock_ints (before)) = 0)) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH32 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH33 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH34 : ((os_sched_lock_ints (before)) <= 0)) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH36 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (0 <= ty)) (PreH39 : (ty <= 255)) (PreH40 : (0 <= (os_sched_lock_ints (before)))) (PreH41 : ((os_sched_lock_ints (before)) <= 255)) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH44 : (p <> 0)) (PreH45 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH46 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH47 : (ptmr_pre <> 0)) (PreH48 : (ptmr_pre = p)) (PreH49 : (perr_pre = error_addr)) (PreH50 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH51 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH52 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH53 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH54 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH55 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH56 : (3 <> status)) (PreH57 : (1 = status)) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 = status) ”
  &&  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_29_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 <> status)) (PreH39 : (0 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
.

Definition OSTmrStart_partial_solve_wit_29_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 <> status)) (PreH39 : (0 = status)) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 = status) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_29 := OSTmrStart_partial_solve_wit_29_pure -> OSTmrStart_partial_solve_wit_29_aux.

Definition OSTmrStart_partial_solve_wit_30_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH13 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH14 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : ((os_sched_lock_ints (before)) <= 0)) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH20 : (0 <= ty)) (PreH21 : (ty <= 255)) (PreH22 : (0 <= (os_sched_lock_ints (before)))) (PreH23 : ((os_sched_lock_ints (before)) <= 255)) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH26 : (p <> 0)) (PreH27 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (ptmr_pre <> 0)) (PreH30 : (ptmr_pre = p)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH36 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (3 <> status)) (PreH39 : (1 <> status)) (PreH40 : (2 <> status)) (PreH41 : (0 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ”
.

Definition OSTmrStart_partial_solve_wit_30_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH13 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH14 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : ((os_sched_lock_ints (before)) <= 0)) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH20 : (0 <= ty)) (PreH21 : (ty <= 255)) (PreH22 : (0 <= (os_sched_lock_ints (before)))) (PreH23 : ((os_sched_lock_ints (before)) <= 255)) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH26 : (p <> 0)) (PreH27 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (ptmr_pre <> 0)) (PreH30 : (ptmr_pre = p)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH36 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (3 <> status)) (PreH39 : (1 <> status)) (PreH40 : (2 <> status)) (PreH41 : (0 = status)) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 = status) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_30 := OSTmrStart_partial_solve_wit_30_pure -> OSTmrStart_partial_solve_wit_30_aux.

Definition OSTmrStart_partial_solve_wit_31_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH11 : (p <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_lock_ints (before)) = 0)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : ((os_sched_lock_ints (before)) <= 0)) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (0 <= ty)) (PreH23 : (ty <= 255)) (PreH24 : (0 <= (os_sched_lock_ints (before)))) (PreH25 : ((os_sched_lock_ints (before)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH28 : (p <> 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (ptmr_pre = p)) (PreH33 : (perr_pre = error_addr)) (PreH34 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH38 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (3 <> status)) (PreH41 : (1 <> status)) (PreH42 : (2 <> status)) (PreH43 : (0 = status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrStart_partial_solve_wit_31_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH11 : (p <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_lock_ints (before)) = 0)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : ((os_sched_lock_ints (before)) <= 0)) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (0 <= ty)) (PreH23 : (ty <= 255)) (PreH24 : (0 <= (os_sched_lock_ints (before)))) (PreH25 : ((os_sched_lock_ints (before)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH28 : (p <> 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (ptmr_pre = p)) (PreH33 : (perr_pre = error_addr)) (PreH34 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH38 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (3 <> status)) (PreH41 : (1 <> status)) (PreH42 : (2 <> status)) (PreH43 : (0 = status)) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 = status) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_31 := OSTmrStart_partial_solve_wit_31_pure -> OSTmrStart_partial_solve_wit_31_aux.

Definition OSTmrStart_partial_solve_wit_32 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH11 : (p <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_lock_ints (before)) = 0)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : ((os_sched_lock_ints (before)) <= 0)) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (0 <= ty)) (PreH23 : (ty <= 255)) (PreH24 : (0 <= (os_sched_lock_ints (before)))) (PreH25 : ((os_sched_lock_ints (before)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH28 : (p <> 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (ptmr_pre = p)) (PreH33 : (perr_pre = error_addr)) (PreH34 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH38 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (3 <> status)) (PreH41 : (1 <> status)) (PreH42 : (2 <> status)) (PreH43 : (0 = status)) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 = status) ”
  &&  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_33 := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH11 : (p <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_lock_ints (before)) = 0)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : ((os_sched_lock_ints (before)) <= 0)) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (0 <= ty)) (PreH23 : (ty <= 255)) (PreH24 : (0 <= (os_sched_lock_ints (before)))) (PreH25 : ((os_sched_lock_ints (before)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH28 : (p <> 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (ptmr_pre = p)) (PreH33 : (perr_pre = error_addr)) (PreH34 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH38 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (3 <> status)) (PreH41 : (1 <> status)) (PreH42 : (2 <> status)) (PreH43 : (0 <> status)) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 <> status) ”
  &&  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_34_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH11 : (p <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_lock_ints (before)) = 0)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : ((os_sched_lock_ints (before)) <= 0)) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (0 <= ty)) (PreH23 : (ty <= 255)) (PreH24 : (0 <= (os_sched_lock_ints (before)))) (PreH25 : ((os_sched_lock_ints (before)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH28 : (p <> 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (ptmr_pre = p)) (PreH33 : (perr_pre = error_addr)) (PreH34 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH38 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (3 <> status)) (PreH41 : (1 <> status)) (PreH42 : (2 <> status)) (PreH43 : (0 <> status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrStart_partial_solve_wit_34_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH4 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH5 : (p <> 0)) (PreH6 : (ty = 100)) (PreH7 : ((os_sched_lock_ints (before)) = 0)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH11 : (p <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_lock_ints (before)) = 0)) (PreH14 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH15 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH16 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : ((os_sched_lock_ints (before)) <= 0)) (PreH19 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH20 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH21 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH22 : (0 <= ty)) (PreH23 : (ty <= 255)) (PreH24 : (0 <= (os_sched_lock_ints (before)))) (PreH25 : ((os_sched_lock_ints (before)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH28 : (p <> 0)) (PreH29 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH30 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (ptmr_pre = p)) (PreH33 : (perr_pre = error_addr)) (PreH34 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH35 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH37 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH38 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH39 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH40 : (3 <> status)) (PreH41 : (1 <> status)) (PreH42 : (2 <> status)) (PreH43 : (0 <> status)) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 <> status) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_34 := OSTmrStart_partial_solve_wit_34_pure -> OSTmrStart_partial_solve_wit_34_aux.

Definition OSTmrStart_partial_solve_wit_35_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH13 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH14 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : ((os_sched_lock_ints (before)) <= 0)) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH20 : (0 <= ty)) (PreH21 : (ty <= 255)) (PreH22 : (0 <= (os_sched_lock_ints (before)))) (PreH23 : ((os_sched_lock_ints (before)) <= 255)) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH26 : (p <> 0)) (PreH27 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (ptmr_pre <> 0)) (PreH30 : (ptmr_pre = p)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH36 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (3 <> status)) (PreH39 : (1 <> status)) (PreH40 : (2 <> status)) (PreH41 : (0 <> status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ”
.

Definition OSTmrStart_partial_solve_wit_35_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) (PreH3 : (p <> 0)) (PreH4 : (ty = 100)) (PreH5 : ((os_sched_lock_ints (before)) = 0)) (PreH6 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH7 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH9 : (p <> 0)) (PreH10 : (ty = 100)) (PreH11 : ((os_sched_lock_ints (before)) = 0)) (PreH12 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH13 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH14 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : ((os_sched_lock_ints (before)) <= 0)) (PreH17 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH18 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH19 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH20 : (0 <= ty)) (PreH21 : (ty <= 255)) (PreH22 : (0 <= (os_sched_lock_ints (before)))) (PreH23 : ((os_sched_lock_ints (before)) <= 255)) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH26 : (p <> 0)) (PreH27 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH28 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH29 : (ptmr_pre <> 0)) (PreH30 : (ptmr_pre = p)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH35 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH36 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH37 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH38 : (3 <> status)) (PreH39 : (1 <> status)) (PreH40 : (2 <> status)) (PreH41 : (0 <> status)) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 <> status) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_35 := OSTmrStart_partial_solve_wit_35_pure -> OSTmrStart_partial_solve_wit_35_aux.

Definition OSTmrStart_partial_solve_wit_36_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 <> status)) (PreH39 : (0 <> status)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status <> 0) ” 
  &&  “ (status <> 1) ” 
  &&  “ (status <> 2) ” 
  &&  “ (status <> 3) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
.

Definition OSTmrStart_partial_solve_wit_36_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (error_addr: Z) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (p <> 0)) (PreH8 : (ty = 100)) (PreH9 : ((os_sched_lock_ints (before)) = 0)) (PreH10 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH11 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH12 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH13 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH14 : ((os_sched_lock_ints (before)) <= 0)) (PreH15 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH16 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH17 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH18 : (0 <= ty)) (PreH19 : (ty <= 255)) (PreH20 : (0 <= (os_sched_lock_ints (before)))) (PreH21 : ((os_sched_lock_ints (before)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((unsigned_last_nbits (ty) (32)) = 100)) (PreH24 : (p <> 0)) (PreH25 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH26 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (ptmr_pre = p)) (PreH29 : (perr_pre = error_addr)) (PreH30 : (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH31 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH33 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH34 : (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg)))) (PreH35 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH36 : (3 <> status)) (PreH37 : (1 <> status)) (PreH38 : (2 <> status)) (PreH39 : (0 <> status)) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status <> 0) ” 
  &&  “ (status <> 1) ” 
  &&  “ (status <> 2) ” 
  &&  “ (status <> 3) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits (ty) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_start_layout p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg))) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (3 <> status) ” 
  &&  “ (1 <> status) ” 
  &&  “ (2 <> status) ” 
  &&  “ (0 <> status) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrStart_partial_solve_wit_36 := OSTmrStart_partial_solve_wit_36_pure -> OSTmrStart_partial_solve_wit_36_aux.

Definition OSTmrStart_which_implies_wit_1 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
|--
  “ (p <> 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_1_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_2 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
).

Definition OSTmrStart_which_implies_wit_2_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH3 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
.

Definition OSTmrStart_which_implies_wit_3 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((os_sched_lock_ints (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_lock_ints (before))) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= ty) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_3_split_goal_1 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTmrStart_which_implies_wit_3_split_goal_2 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ ((os_sched_lock_ints (before)) <= 255) ”
.

Definition OSTmrStart_which_implies_wit_3_split_goal_3 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (0 <= (os_sched_lock_ints (before))) ”
.

Definition OSTmrStart_which_implies_wit_3_split_goal_4 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (ty <= 255) ”
.

Definition OSTmrStart_which_implies_wit_3_split_goal_5 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  “ (0 <= ty) ”
.

Definition OSTmrStart_which_implies_wit_3_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (p <> 0)) (PreH3 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  (tmr_start_type_rest external platform sg context mask pooled p i ty raw_state before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_4 := 
(
forall (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
) \/
(
forall (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
|--
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
).

Definition OSTmrStart_which_implies_wit_4_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
|--
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before before )
.

Definition OSTmrStart_which_implies_wit_5 := 
(
forall (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
) \/
(
forall (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_5_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (before)))
  **  (tmr_start_int_rest external platform sg context mask pooled p ty raw_state before )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_6 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
|--
  EX (status: Z)  (lock_entry: UCOS2_Verify_State)  (locked: UCOS2_Verify_State) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
|--
  EX (status: Z)  (lock_entry: UCOS2_Verify_State)  (locked: UCOS2_Verify_State) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
).

Definition OSTmrStart_which_implies_wit_7 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
).

Definition OSTmrStart_which_implies_wit_7_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH5 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
.

Definition OSTmrStart_which_implies_wit_8 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (status = 3) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_unlink_running (TimerState (locked)) i ) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_unlink_running (TimerState (locked)) i ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (pooled = true) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
).

Definition OSTmrStart_which_implies_wit_8_split_goal_1 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_unlink_running (TimerState (locked)) i ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_2 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (timer_api_initialized (TimerState (locked)) ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_3 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (UCOS2_state_inv sg locked ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_4 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_unlink_profile sg ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_5 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_link_profile sg ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_6 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_unlink_layout ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_7 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_link_layout ) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_8 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (p = (timer_pool_addr (sg) (i))) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_9 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (pooled = true) ”
.

Definition OSTmrStart_which_implies_wit_8_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 3)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
.

Definition OSTmrStart_which_implies_wit_9 := 
(
forall (i: Z) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg locked )) (PreH2 : (timer_api_initialized (TimerState (locked)) )) (PreH3 : (tmr_link_profile sg )) (PreH4 : (tmr_unlink_running (TimerState (locked)) i )) ,
  (tmr_unlink_configured_post sg (TimerState (locked)) i )
  **  (tmr_start_timer_frame external platform sg context mask locked )
|--
  EX (stopped: GlobTimerState) ,
  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ”
  &&  (timer_inv sg stopped )
  **  (tmr_start_timer_frame external platform sg context mask locked )
) \/
(
forall (i: Z) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg locked )) (PreH2 : (timer_api_initialized (TimerState (locked)) )) (PreH3 : (tmr_link_profile sg )) (PreH4 : (tmr_unlink_running (TimerState (locked)) i )) ,
  (tmr_unlink_configured_post sg (TimerState (locked)) i )
  **  (tmr_start_timer_frame external platform sg context mask locked )
|--
  EX (stopped: GlobTimerState) ,
  “ (tmr_start_unlinked sg (TimerState (locked)) i stopped ) ” 
  &&  “ (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) ) ” 
  &&  “ (timer_api_initialized stopped ) ” 
  &&  “ (tmr_link_eligible stopped i ) ”
  &&  (timer_inv sg stopped )
  **  (tmr_start_timer_frame external platform sg context mask locked )
).

Definition OSTmrStart_which_implies_wit_10 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (pooled = true)) (PreH8 : (status = 3)) (PreH9 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH10 : (tmr_link_eligible stopped i )) (PreH11 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH12 : (timer_api_initialized stopped )) ,
  (tmr_link_configured_post sg stopped i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
|--
  EX (started: GlobTimerState) ,
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (stopped: GlobTimerState) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (pooled = true)) (PreH8 : (status = 3)) (PreH9 : (tmr_start_unlinked sg (TimerState (locked)) i stopped )) (PreH10 : (tmr_link_eligible stopped i )) (PreH11 : (UCOS2_state_inv sg (replace_TimerS (stopped) (locked)) )) (PreH12 : (timer_api_initialized stopped )) ,
  (tmr_link_configured_post sg stopped i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
|--
  EX (started: GlobTimerState) ,
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
).

Definition OSTmrStart_which_implies_wit_11 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
|--
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_11_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
|--
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_12 := 
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (started: GlobTimerState) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (started: GlobTimerState) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
).

Definition OSTmrStart_which_implies_wit_13 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_lock_ints (before)) = 0) ” 
  &&  “ (tmr_start_nonrunning_status status ) ” 
  &&  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked ) ” 
  &&  “ (tmr_start_current sg pooled p i raw_state status locked ) ” 
  &&  “ (pooled = true) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (tmr_link_eligible (TimerState (locked)) i ) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_link_eligible (TimerState (locked)) i ) ” 
  &&  “ (timer_api_initialized (TimerState (locked)) ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (tmr_link_profile sg ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_link_layout ) ” 
  &&  “ (p = (timer_pool_addr (sg) (i))) ” 
  &&  “ (pooled = true) ”
  &&  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
).

Definition OSTmrStart_which_implies_wit_13_split_goal_1 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_link_eligible (TimerState (locked)) i ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_2 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (timer_api_initialized (TimerState (locked)) ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_3 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (UCOS2_state_inv sg locked ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_4 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_unlink_profile sg ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_5 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_link_profile sg ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_6 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_unlink_layout ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_7 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_link_layout ) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_8 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (p = (timer_pool_addr (sg) (i))) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_9 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (pooled = true) ”
.

Definition OSTmrStart_which_implies_wit_13_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_nonrunning_status status )) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  (timer_inv sg (TimerState (locked)) )
  **  (tmr_start_timer_frame external platform sg context mask locked )
.

Definition OSTmrStart_which_implies_wit_14 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (pooled = true)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_link_eligible (TimerState (locked)) i )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (timer_api_initialized (TimerState (locked)) )) ,
  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
|--
  EX (started: GlobTimerState) ,
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH5 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH6 : (tmr_start_current sg pooled p i raw_state status locked )) (PreH7 : (pooled = true)) (PreH8 : (tmr_start_nonrunning_status status )) (PreH9 : (tmr_link_eligible (TimerState (locked)) i )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (timer_api_initialized (TimerState (locked)) )) ,
  (tmr_link_configured_post sg (TimerState (locked)) i 0 )
  **  (tmr_start_timer_frame external platform sg context mask locked )
|--
  EX (started: GlobTimerState) ,
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
).

Definition OSTmrStart_which_implies_wit_15 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
|--
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_15_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (started: GlobTimerState) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 1 0 before lock_entry locked (replace_TimerS (started) (locked)) )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before (replace_TimerS (started) (locked)) )
|--
  (os_sched_unlock_pre external platform critical sg context mask (replace_TimerS (started) (locked)) )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_16 := 
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (started: GlobTimerState) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (started: GlobTimerState) ,
  (os_sched_unlock_post external platform critical sg context mask (replace_TimerS (started) (locked)) )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context (replace_TimerS (started) (locked)) returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
).

Definition OSTmrStart_which_implies_wit_17 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 0)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 0)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_start_prefix critical sg context pooled p i 100 raw_state 0 135 before lock_entry locked locked ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
).

Definition OSTmrStart_which_implies_wit_17_split_goal_1 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 0)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_start_prefix critical sg context pooled p i 100 raw_state 0 135 before lock_entry locked locked ) ”
.

Definition OSTmrStart_which_implies_wit_17_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status = 0)) (PreH5 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH6 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH7 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH8 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
.

Definition OSTmrStart_which_implies_wit_18 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_18_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 135 before lock_entry locked locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_19 := 
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context locked returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context locked returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
).

Definition OSTmrStart_which_implies_wit_20 := 
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context locked returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State) ,
  “ (tmr_start_unlock_return external critical sg context locked returned final ) ”
  &&  (tmr_start_return_resources external platform critical sg context returned mask final )
).

Definition OSTmrStart_which_implies_wit_21 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
).

Definition OSTmrStart_which_implies_wit_21_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (PreH1 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH2 : (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked )) ,
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_start_raw_rep pooled p ty raw_state before )
.

Definition OSTmrStart_which_implies_wit_22 := 
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status <> 0)) (PreH5 : (status <> 1)) (PreH6 : (status <> 2)) (PreH7 : (status <> 3)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ) ” 
  &&  “ (tmr_start_prefix critical sg context pooled p i ty raw_state 0 141 before lock_entry locked locked ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
) \/
(
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status <> 0)) (PreH5 : (status <> 1)) (PreH6 : (status <> 2)) (PreH7 : (status <> 3)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_start_prefix critical sg context pooled p i 100 raw_state 0 141 before lock_entry locked locked ) ”
  &&  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
).

Definition OSTmrStart_which_implies_wit_22_split_goal_1 := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status <> 0)) (PreH5 : (status <> 1)) (PreH6 : (status <> 2)) (PreH7 : (status <> 3)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  “ (tmr_start_prefix critical sg context pooled p i 100 raw_state 0 141 before lock_entry locked locked ) ”
.

Definition OSTmrStart_which_implies_wit_22_split_goal_spatial := 
forall (X: (tmr_start_result -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (raw_state: Z) (ty: Z) (i: Z) (p: Z) (pooled: bool) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (lock_entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (status: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_lock_ints (before)) = 0)) (PreH4 : (status <> 0)) (PreH5 : (status <> 1)) (PreH6 : (status <> 2)) (PreH7 : (status <> 3)) (PreH8 : (tmr_start_layout p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") )) (PreH9 : (tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X )) (PreH10 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before lock_entry locked )) (PreH11 : (tmr_start_current sg pooled p i raw_state status locked )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> status)
  **  (tmr_start_state_rest external platform sg context mask pooled p i ty raw_state status before locked )
|--
  (tmr_start_owned external platform sg context mask pooled p ty raw_state before locked )
.

Module Type VC_Correct.


Axiom proof_of_OSTmrStart_safety_wit_1 : OSTmrStart_safety_wit_1.
Axiom proof_of_OSTmrStart_return_wit_1 : OSTmrStart_return_wit_1.
Axiom proof_of_OSTmrStart_return_wit_2 : OSTmrStart_return_wit_2.
Axiom proof_of_OSTmrStart_return_wit_3 : OSTmrStart_return_wit_3.
Axiom proof_of_OSTmrStart_return_wit_4 : OSTmrStart_return_wit_4.
Axiom proof_of_OSTmrStart_return_wit_5 : OSTmrStart_return_wit_5.
Axiom proof_of_OSTmrStart_return_wit_6 : OSTmrStart_return_wit_6.
Axiom proof_of_OSTmrStart_return_wit_7 : OSTmrStart_return_wit_7.
Axiom proof_of_OSTmrStart_return_wit_8 : OSTmrStart_return_wit_8.
Axiom proof_of_OSTmrStart_partial_solve_wit_1_pure : OSTmrStart_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_1 : OSTmrStart_partial_solve_wit_1.
Axiom proof_of_OSTmrStart_partial_solve_wit_2_pure : OSTmrStart_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_2 : OSTmrStart_partial_solve_wit_2.
Axiom proof_of_OSTmrStart_partial_solve_wit_3_pure : OSTmrStart_partial_solve_wit_3_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_3 : OSTmrStart_partial_solve_wit_3.
Axiom proof_of_OSTmrStart_partial_solve_wit_4_pure : OSTmrStart_partial_solve_wit_4_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_4 : OSTmrStart_partial_solve_wit_4.
Axiom proof_of_OSTmrStart_partial_solve_wit_5_pure : OSTmrStart_partial_solve_wit_5_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_5 : OSTmrStart_partial_solve_wit_5.
Axiom proof_of_OSTmrStart_partial_solve_wit_6_pure : OSTmrStart_partial_solve_wit_6_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_6 : OSTmrStart_partial_solve_wit_6.
Axiom proof_of_OSTmrStart_partial_solve_wit_7_pure : OSTmrStart_partial_solve_wit_7_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_7 : OSTmrStart_partial_solve_wit_7.
Axiom proof_of_OSTmrStart_partial_solve_wit_8_pure : OSTmrStart_partial_solve_wit_8_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_8 : OSTmrStart_partial_solve_wit_8.
Axiom proof_of_OSTmrStart_partial_solve_wit_9_pure : OSTmrStart_partial_solve_wit_9_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_9 : OSTmrStart_partial_solve_wit_9.
Axiom proof_of_OSTmrStart_partial_solve_wit_10_pure : OSTmrStart_partial_solve_wit_10_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_10 : OSTmrStart_partial_solve_wit_10.
Axiom proof_of_OSTmrStart_partial_solve_wit_11_pure : OSTmrStart_partial_solve_wit_11_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_11 : OSTmrStart_partial_solve_wit_11.
Axiom proof_of_OSTmrStart_partial_solve_wit_12_pure : OSTmrStart_partial_solve_wit_12_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_12 : OSTmrStart_partial_solve_wit_12.
Axiom proof_of_OSTmrStart_partial_solve_wit_13_pure : OSTmrStart_partial_solve_wit_13_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_13 : OSTmrStart_partial_solve_wit_13.
Axiom proof_of_OSTmrStart_partial_solve_wit_14_pure : OSTmrStart_partial_solve_wit_14_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_14 : OSTmrStart_partial_solve_wit_14.
Axiom proof_of_OSTmrStart_partial_solve_wit_15_pure : OSTmrStart_partial_solve_wit_15_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_15 : OSTmrStart_partial_solve_wit_15.
Axiom proof_of_OSTmrStart_partial_solve_wit_16 : OSTmrStart_partial_solve_wit_16.
Axiom proof_of_OSTmrStart_partial_solve_wit_17_pure : OSTmrStart_partial_solve_wit_17_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_17 : OSTmrStart_partial_solve_wit_17.
Axiom proof_of_OSTmrStart_partial_solve_wit_18_pure : OSTmrStart_partial_solve_wit_18_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_18 : OSTmrStart_partial_solve_wit_18.
Axiom proof_of_OSTmrStart_partial_solve_wit_19_pure : OSTmrStart_partial_solve_wit_19_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_19 : OSTmrStart_partial_solve_wit_19.
Axiom proof_of_OSTmrStart_partial_solve_wit_20_pure : OSTmrStart_partial_solve_wit_20_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_20 : OSTmrStart_partial_solve_wit_20.
Axiom proof_of_OSTmrStart_partial_solve_wit_21_pure : OSTmrStart_partial_solve_wit_21_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_21 : OSTmrStart_partial_solve_wit_21.
Axiom proof_of_OSTmrStart_partial_solve_wit_22_pure : OSTmrStart_partial_solve_wit_22_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_22 : OSTmrStart_partial_solve_wit_22.
Axiom proof_of_OSTmrStart_partial_solve_wit_23_pure : OSTmrStart_partial_solve_wit_23_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_23 : OSTmrStart_partial_solve_wit_23.
Axiom proof_of_OSTmrStart_partial_solve_wit_24_pure : OSTmrStart_partial_solve_wit_24_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_24 : OSTmrStart_partial_solve_wit_24.
Axiom proof_of_OSTmrStart_partial_solve_wit_25_pure : OSTmrStart_partial_solve_wit_25_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_25 : OSTmrStart_partial_solve_wit_25.
Axiom proof_of_OSTmrStart_partial_solve_wit_26_pure : OSTmrStart_partial_solve_wit_26_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_26 : OSTmrStart_partial_solve_wit_26.
Axiom proof_of_OSTmrStart_partial_solve_wit_27 : OSTmrStart_partial_solve_wit_27.
Axiom proof_of_OSTmrStart_partial_solve_wit_28 : OSTmrStart_partial_solve_wit_28.
Axiom proof_of_OSTmrStart_partial_solve_wit_29_pure : OSTmrStart_partial_solve_wit_29_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_29 : OSTmrStart_partial_solve_wit_29.
Axiom proof_of_OSTmrStart_partial_solve_wit_30_pure : OSTmrStart_partial_solve_wit_30_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_30 : OSTmrStart_partial_solve_wit_30.
Axiom proof_of_OSTmrStart_partial_solve_wit_31_pure : OSTmrStart_partial_solve_wit_31_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_31 : OSTmrStart_partial_solve_wit_31.
Axiom proof_of_OSTmrStart_partial_solve_wit_32 : OSTmrStart_partial_solve_wit_32.
Axiom proof_of_OSTmrStart_partial_solve_wit_33 : OSTmrStart_partial_solve_wit_33.
Axiom proof_of_OSTmrStart_partial_solve_wit_34_pure : OSTmrStart_partial_solve_wit_34_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_34 : OSTmrStart_partial_solve_wit_34.
Axiom proof_of_OSTmrStart_partial_solve_wit_35_pure : OSTmrStart_partial_solve_wit_35_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_35 : OSTmrStart_partial_solve_wit_35.
Axiom proof_of_OSTmrStart_partial_solve_wit_36_pure : OSTmrStart_partial_solve_wit_36_pure.
Axiom proof_of_OSTmrStart_partial_solve_wit_36 : OSTmrStart_partial_solve_wit_36.
Axiom proof_of_OSTmrStart_which_implies_wit_1 : OSTmrStart_which_implies_wit_1.
Axiom proof_of_OSTmrStart_which_implies_wit_2 : OSTmrStart_which_implies_wit_2.
Axiom proof_of_OSTmrStart_which_implies_wit_3 : OSTmrStart_which_implies_wit_3.
Axiom proof_of_OSTmrStart_which_implies_wit_4 : OSTmrStart_which_implies_wit_4.
Axiom proof_of_OSTmrStart_which_implies_wit_5 : OSTmrStart_which_implies_wit_5.
Axiom proof_of_OSTmrStart_which_implies_wit_6 : OSTmrStart_which_implies_wit_6.
Axiom proof_of_OSTmrStart_which_implies_wit_7 : OSTmrStart_which_implies_wit_7.
Axiom proof_of_OSTmrStart_which_implies_wit_8 : OSTmrStart_which_implies_wit_8.
Axiom proof_of_OSTmrStart_which_implies_wit_9 : OSTmrStart_which_implies_wit_9.
Axiom proof_of_OSTmrStart_which_implies_wit_10 : OSTmrStart_which_implies_wit_10.
Axiom proof_of_OSTmrStart_which_implies_wit_11 : OSTmrStart_which_implies_wit_11.
Axiom proof_of_OSTmrStart_which_implies_wit_12 : OSTmrStart_which_implies_wit_12.
Axiom proof_of_OSTmrStart_which_implies_wit_13 : OSTmrStart_which_implies_wit_13.
Axiom proof_of_OSTmrStart_which_implies_wit_14 : OSTmrStart_which_implies_wit_14.
Axiom proof_of_OSTmrStart_which_implies_wit_15 : OSTmrStart_which_implies_wit_15.
Axiom proof_of_OSTmrStart_which_implies_wit_16 : OSTmrStart_which_implies_wit_16.
Axiom proof_of_OSTmrStart_which_implies_wit_17 : OSTmrStart_which_implies_wit_17.
Axiom proof_of_OSTmrStart_which_implies_wit_18 : OSTmrStart_which_implies_wit_18.
Axiom proof_of_OSTmrStart_which_implies_wit_19 : OSTmrStart_which_implies_wit_19.
Axiom proof_of_OSTmrStart_which_implies_wit_20 : OSTmrStart_which_implies_wit_20.
Axiom proof_of_OSTmrStart_which_implies_wit_21 : OSTmrStart_which_implies_wit_21.
Axiom proof_of_OSTmrStart_which_implies_wit_22 : OSTmrStart_which_implies_wit_22.

End VC_Correct.
