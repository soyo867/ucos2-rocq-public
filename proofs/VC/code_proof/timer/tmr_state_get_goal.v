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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_state_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmrStateGet -----*)

Definition OSTmrStateGet_safety_wit_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = p)) (PreH2 : (perr_pre = error_addr)) (PreH3 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrStateGet_entail_wit_1_1 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 = observed)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (F )
|--
  EX (error: Z) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (0))) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
).

Definition OSTmrStateGet_entail_wit_1_1_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (0))) ”
.

Definition OSTmrStateGet_entail_wit_1_1_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
.

Definition OSTmrStateGet_entail_wit_1_2 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 = observed)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (F )
|--
  EX (error: Z) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (1))) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
).

Definition OSTmrStateGet_entail_wit_1_2_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (1))) ”
.

Definition OSTmrStateGet_entail_wit_1_2_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
.

Definition OSTmrStateGet_entail_wit_1_3 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 = observed)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (F )
|--
  EX (error: Z) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (2))) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
).

Definition OSTmrStateGet_entail_wit_1_3_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (2))) ”
.

Definition OSTmrStateGet_entail_wit_1_3_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
.

Definition OSTmrStateGet_entail_wit_1_4 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 = observed)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (F )
|--
  EX (error: Z) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (3))) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
).

Definition OSTmrStateGet_entail_wit_1_4_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (0 = (tmr_state_get_state_error (3))) ”
.

Definition OSTmrStateGet_entail_wit_1_4_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 = observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
.

Definition OSTmrStateGet_entail_wit_1_5 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 <> observed)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 141)
  **  (F )
|--
  EX (error: Z) ,
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 <> observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (141 = (tmr_state_get_state_error (observed))) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
).

Definition OSTmrStateGet_entail_wit_1_5_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 <> observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  “ (141 = (tmr_state_get_state_error (observed))) ”
.

Definition OSTmrStateGet_entail_wit_1_5_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH8 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH9 : (UCOS2_state_inv sg locked )) (PreH10 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH11 : (ptmr_pre <> 0)) (PreH12 : (ty = 100)) (PreH13 : ((os_sched_ints (before)) = 0)) (PreH14 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH16 : ((os_sched_ints (before)) <= 0)) (PreH17 : (ty = 100)) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (0 <= ty)) (PreH20 : (ty <= 255)) (PreH21 : (0 <= (os_sched_ints (before)))) (PreH22 : ((os_sched_ints (before)) <= 255)) (PreH23 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH25 : (ptmr_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH29 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (0 <> observed)) (PreH31 : (1 <> observed)) (PreH32 : (2 <> observed)) (PreH33 : (3 <> observed)) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr_pre raw i ty observed )
  **  (F )
|--
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  (F )
.

Definition OSTmrStateGet_return_wit_1 := 
(
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH8 : (p <> 0)) (PreH9 : (ty = 100)) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : (0 <= observed)) (PreH12 : (observed <= 255)) (PreH13 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (error = (tmr_state_get_state_error (observed)))) (PreH15 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH17 : (UCOS2_state_inv sg locked )) (PreH18 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage p raw ty raw_state before )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr observed X )
  **  (F )
) \/
(
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH8 : (p <> 0)) (PreH9 : (ty = 100)) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : (0 <= observed)) (PreH12 : (observed <= 255)) (PreH13 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (error = (tmr_state_get_state_error (observed)))) (PreH15 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH17 : (UCOS2_state_inv sg locked )) (PreH18 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage p raw ty raw_state before )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr observed X )
  **  (F )
).

Definition OSTmrStateGet_return_wit_1_split_goal_spatial := 
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH8 : (p <> 0)) (PreH9 : (ty = 100)) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : (0 <= observed)) (PreH12 : (observed <= 255)) (PreH13 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (error = (tmr_state_get_state_error (observed)))) (PreH15 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH17 : (UCOS2_state_inv sg locked )) (PreH18 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage p raw ty raw_state before )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr observed X )
  **  (F )
.

Definition OSTmrStateGet_return_wit_2 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_ints (before)) > 0)) (PreH2 : (ty = 100)) (PreH3 : (ptmr_pre <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (os_sched_ints (before)))) (PreH7 : ((os_sched_ints (before)) <= 255)) (PreH8 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |-> 139)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_ints (before)) > 0)) (PreH2 : (ty = 100)) (PreH3 : (ptmr_pre <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (os_sched_ints (before)))) (PreH7 : ((os_sched_ints (before)) <= 255)) (PreH8 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |-> 139)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
).

Definition OSTmrStateGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_ints (before)) > 0)) (PreH2 : (ty = 100)) (PreH3 : (ptmr_pre <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (os_sched_ints (before)))) (PreH7 : ((os_sched_ints (before)) <= 255)) (PreH8 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |-> 139)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
.

Definition OSTmrStateGet_return_wit_3 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ty <> 100)) (PreH2 : (ptmr_pre <> 0)) (PreH3 : (0 <= ty)) (PreH4 : (ty <= 255)) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH9 : (ptmr_pre <> 0)) (PreH10 : (ptmr_pre = p)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |-> 137)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ty <> 100)) (PreH2 : (ptmr_pre <> 0)) (PreH3 : (0 <= ty)) (PreH4 : (ty <= 255)) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH9 : (ptmr_pre <> 0)) (PreH10 : (ptmr_pre = p)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |-> 137)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
).

Definition OSTmrStateGet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ty <> 100)) (PreH2 : (ptmr_pre <> 0)) (PreH3 : (0 <= ty)) (PreH4 : (ty <= 255)) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH9 : (ptmr_pre <> 0)) (PreH10 : (ptmr_pre = p)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |-> 137)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
.

Definition OSTmrStateGet_return_wit_4 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |-> 138)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |-> 138)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
).

Definition OSTmrStateGet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |-> 138)
  **  (F )
|--
  (tmr_state_get_post external platform critical sg context mask before p raw i ty raw_state error_addr 0 X )
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (ptmr_pre <> 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
.

Definition OSTmrStateGet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (ptmr_pre <> 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (tmr_state_get_pre external platform critical sg context mask before ptmr_pre raw i ty raw_state X )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_1 := OSTmrStateGet_partial_solve_wit_1_pure -> OSTmrStateGet_partial_solve_wit_1_aux.

Definition OSTmrStateGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_ints (before)) <= 0)) (PreH2 : (ty = 100)) (PreH3 : (ptmr_pre <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (os_sched_ints (before)))) (PreH7 : ((os_sched_ints (before)) <= 255)) (PreH8 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (ptmr_pre <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ”
.

Definition OSTmrStateGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((os_sched_ints (before)) <= 0)) (PreH2 : (ty = 100)) (PreH3 : (ptmr_pre <> 0)) (PreH4 : (0 <= ty)) (PreH5 : (ty <= 255)) (PreH6 : (0 <= (os_sched_ints (before)))) (PreH7 : ((os_sched_ints (before)) <= 255)) (PreH8 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr_pre = p)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (ptmr_pre <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ ((os_sched_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr_pre raw i ty raw_state )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_2 := OSTmrStateGet_partial_solve_wit_2_pure -> OSTmrStateGet_partial_solve_wit_2_aux.

Definition OSTmrStateGet_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH6 : ((os_sched_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (os_sched_ints (before)))) (PreH12 : ((os_sched_ints (before)) <= 255)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH6 : ((os_sched_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (os_sched_ints (before)))) (PreH12 : ((os_sched_ints (before)) <= 255)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
).

Definition OSTmrStateGet_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH6 : ((os_sched_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (os_sched_ints (before)))) (PreH12 : ((os_sched_ints (before)) <= 255)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrStateGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH6 : ((os_sched_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (os_sched_ints (before)))) (PreH12 : ((os_sched_ints (before)) <= 255)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ ((os_sched_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_3 := OSTmrStateGet_partial_solve_wit_3_pure -> OSTmrStateGet_partial_solve_wit_3_aux.

Definition OSTmrStateGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH6 : ((os_sched_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (os_sched_ints (before)))) (PreH12 : ((os_sched_ints (before)) <= 255)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((( &( "state" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (ptmr_pre <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ”
.

Definition OSTmrStateGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH6 : ((os_sched_ints (before)) <= 0)) (PreH7 : (ty = 100)) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (0 <= ty)) (PreH10 : (ty <= 255)) (PreH11 : (0 <= (os_sched_ints (before)))) (PreH12 : ((os_sched_ints (before)) <= 255)) (PreH13 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (ptmr_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
|--
  “ (ptmr_pre <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ ((os_sched_ints (before)) <= 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr_pre raw i ty raw_state X ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_state_get_layout sg ptmr_pre &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr_pre raw ty raw_state before )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_4 := OSTmrStateGet_partial_solve_wit_4_pure -> OSTmrStateGet_partial_solve_wit_4_aux.

Definition OSTmrStateGet_partial_solve_wit_5_pure := 
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (error = (tmr_state_get_state_error (observed)))) (PreH8 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH9 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "state" ) )) # UChar  |-> observed)
  **  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ”
.

Definition OSTmrStateGet_partial_solve_wit_5_aux := 
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (0 <= observed)) (PreH5 : (observed <= 255)) (PreH6 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (error = (tmr_state_get_state_error (observed)))) (PreH8 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH9 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((p)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked p raw i ty observed )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_5 := OSTmrStateGet_partial_solve_wit_5_pure -> OSTmrStateGet_partial_solve_wit_5_aux.

Definition OSTmrStateGet_partial_solve_wit_6_pure := 
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH8 : (p <> 0)) (PreH9 : (ty = 100)) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : (0 <= observed)) (PreH12 : (observed <= 255)) (PreH13 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (error = (tmr_state_get_state_error (observed)))) (PreH15 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH17 : (UCOS2_state_inv sg locked )) (PreH18 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage p raw ty raw_state before )
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "state" ) )) # UChar  |-> observed)
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrStateGet_partial_solve_wit_6_aux := 
forall (F: Assertion) (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (error_addr: Z) (p: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (error: Z) (PreH1 : (p <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH8 : (p <> 0)) (PreH9 : (ty = 100)) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : (0 <= observed)) (PreH12 : (observed <= 255)) (PreH13 : (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : (error = (tmr_state_get_state_error (observed)))) (PreH15 : (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X )) (PreH16 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH17 : (UCOS2_state_inv sg locked )) (PreH18 : (tmr_state_get_observation raw i raw_state locked observed )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage p raw ty raw_state before )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (error = (tmr_state_get_state_error (observed))) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage p raw ty raw_state before )
  **  ((error_addr) # UChar  |-> error)
  **  (F )
.

Definition OSTmrStateGet_partial_solve_wit_6 := OSTmrStateGet_partial_solve_wit_6_pure -> OSTmrStateGet_partial_solve_wit_6_aux.

Definition OSTmrStateGet_which_implies_wit_1 := 
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ (ptmr <> 0) ” 
  &&  “ (0 <= ty) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr raw i ty raw_state )
) \/
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ (ty <= 255) ” 
  &&  “ (0 <= ty) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr raw i ty raw_state )
).

Definition OSTmrStateGet_which_implies_wit_1_split_goal_1 := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ”
.

Definition OSTmrStateGet_which_implies_wit_1_split_goal_2 := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ ((os_sched_ints (before)) <= 255) ”
.

Definition OSTmrStateGet_which_implies_wit_1_split_goal_3 := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ (0 <= (os_sched_ints (before))) ”
.

Definition OSTmrStateGet_which_implies_wit_1_split_goal_4 := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ (ty <= 255) ”
.

Definition OSTmrStateGet_which_implies_wit_1_split_goal_5 := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  “ (0 <= ty) ”
.

Definition OSTmrStateGet_which_implies_wit_1_split_goal_spatial := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_state_get_pre external platform critical sg context mask before ptmr raw i ty raw_state X )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr raw i ty raw_state )
.

Definition OSTmrStateGet_which_implies_wit_2 := 
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr raw i ty raw_state )
|--
  “ (ptmr <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
) \/
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr raw i ty raw_state )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
).

Definition OSTmrStateGet_which_implies_wit_2_split_goal_spatial := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> ty)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (tmr_state_get_observation_frame external platform sg context mask before ptmr raw i ty raw_state )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
.

Definition OSTmrStateGet_which_implies_wit_3 := 
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
|--
  EX (entry: UCOS2_Verify_State)  (locked: UCOS2_Verify_State)  (observed: Z) ,
  “ (ptmr <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr raw i ty observed )
) \/
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
|--
  EX (entry: UCOS2_Verify_State)  (locked: UCOS2_Verify_State)  (observed: Z) ,
  “ (ptmr <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (0 <= observed) ” 
  &&  “ (observed <= 255) ” 
  &&  “ (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr raw i ty observed )
).

Definition OSTmrStateGet_which_implies_wit_4 := 
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (UCOS2_state_inv sg locked )) (PreH8 : (tmr_state_get_observation raw i raw_state locked observed )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr raw i ty observed )
|--
  “ (ptmr <> 0) ” 
  &&  “ (ty = 100) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X ) ” 
  &&  “ (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked ) ” 
  &&  “ (tmr_state_get_observation raw i raw_state locked observed ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
) \/
(
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (UCOS2_state_inv sg locked )) (PreH8 : (tmr_state_get_observation raw i raw_state locked observed )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr raw i ty observed )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
).

Definition OSTmrStateGet_which_implies_wit_4_split_goal_spatial := 
forall (X: (tmr_state_get_result -> (UCOS2_Verify_State -> Prop))) (raw_state: Z) (ty: Z) (i: Z) (raw: bool) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (locked: UCOS2_Verify_State) (observed: Z) (ptmr: Z) (PreH1 : (ptmr <> 0)) (PreH2 : (ty = 100)) (PreH3 : ((os_sched_ints (before)) = 0)) (PreH4 : (tmr_state_get_layout sg ptmr &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (tmr_state_get_entry_facts external critical sg context before ptmr raw i ty raw_state X )) (PreH6 : (os_sched_lock_call_relation critical sg (os_sched_call_invocation (context)) before entry locked )) (PreH7 : (UCOS2_state_inv sg locked )) (PreH8 : (tmr_state_get_observation raw i raw_state locked observed )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> observed)
  **  (tmr_state_get_state_frame external platform critical sg context mask locked ptmr raw i ty observed )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_state_get_raw_storage ptmr raw ty raw_state before )
.

Module Type VC_Correct.


Axiom proof_of_OSTmrStateGet_safety_wit_1 : OSTmrStateGet_safety_wit_1.
Axiom proof_of_OSTmrStateGet_entail_wit_1_1 : OSTmrStateGet_entail_wit_1_1.
Axiom proof_of_OSTmrStateGet_entail_wit_1_2 : OSTmrStateGet_entail_wit_1_2.
Axiom proof_of_OSTmrStateGet_entail_wit_1_3 : OSTmrStateGet_entail_wit_1_3.
Axiom proof_of_OSTmrStateGet_entail_wit_1_4 : OSTmrStateGet_entail_wit_1_4.
Axiom proof_of_OSTmrStateGet_entail_wit_1_5 : OSTmrStateGet_entail_wit_1_5.
Axiom proof_of_OSTmrStateGet_return_wit_1 : OSTmrStateGet_return_wit_1.
Axiom proof_of_OSTmrStateGet_return_wit_2 : OSTmrStateGet_return_wit_2.
Axiom proof_of_OSTmrStateGet_return_wit_3 : OSTmrStateGet_return_wit_3.
Axiom proof_of_OSTmrStateGet_return_wit_4 : OSTmrStateGet_return_wit_4.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_1_pure : OSTmrStateGet_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_1 : OSTmrStateGet_partial_solve_wit_1.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_2_pure : OSTmrStateGet_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_2 : OSTmrStateGet_partial_solve_wit_2.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_3_pure : OSTmrStateGet_partial_solve_wit_3_pure.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_3 : OSTmrStateGet_partial_solve_wit_3.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_4_pure : OSTmrStateGet_partial_solve_wit_4_pure.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_4 : OSTmrStateGet_partial_solve_wit_4.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_5_pure : OSTmrStateGet_partial_solve_wit_5_pure.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_5 : OSTmrStateGet_partial_solve_wit_5.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_6_pure : OSTmrStateGet_partial_solve_wit_6_pure.
Axiom proof_of_OSTmrStateGet_partial_solve_wit_6 : OSTmrStateGet_partial_solve_wit_6.
Axiom proof_of_OSTmrStateGet_which_implies_wit_1 : OSTmrStateGet_which_implies_wit_1.
Axiom proof_of_OSTmrStateGet_which_implies_wit_2 : OSTmrStateGet_which_implies_wit_2.
Axiom proof_of_OSTmrStateGet_which_implies_wit_3 : OSTmrStateGet_which_implies_wit_3.
Axiom proof_of_OSTmrStateGet_which_implies_wit_4 : OSTmrStateGet_which_implies_wit_4.

End VC_Correct.
