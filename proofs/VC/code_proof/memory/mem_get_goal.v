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
Require Import Ucos2Verify.VC.code.memory.spec.mem_get_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSMemGet -----*)

Definition OSMemGet_safety_wit_1 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (perr_pre = error_addr)) (PreH3 : (mem_get_profile sg )) (PreH4 : (mem_get_call_domain critical sg invocation view pe before )) (PreH5 : (mem_get_safe critical sg invocation view pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemGet_safety_wit_2 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_get_profile sg )) (PreH5 : (mem_get_call_domain critical sg invocation view pe before )) (PreH6 : (mem_get_safe critical sg invocation view pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |-> 96)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemGet_safety_wit_3 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (pmem_pre <> 0)) (PreH5 : (pmem_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (mem_get_profile sg )) (PreH8 : (mem_get_call_domain critical sg invocation view pe before )) (PreH9 : (mem_get_safe critical sg invocation view pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemGet_safety_wit_4 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_get_access_checkpoint (entry_2) (access)) current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : ((memImageFree ((mem_get_access_image (access)))) = (mem_get_pointer ((mem_get_access_outcome (access)))))) (PreH5 : ((mem_get_error ((mem_get_access_outcome (access)))) = 0)) (PreH6 : (mem_get_protected sg view pe entry_2 (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry_2) (access)) )) (PreH7 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (mem_get_profile sg )) (PreH17 : (critical_region_interval critical sg invocation before entry_2 )) (PreH18 : (UCOS2_state_inv sg entry_2 )) (PreH19 : (interrupt_saved_value mask retval )) (PreH20 : (mem_get_access_matches sg view pe entry_2 access )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (UCOS2_state_inv sg entry )) (PreH23 : (interrupt_saved_value mask retval )) (PreH24 : (pmem_pre <> 0)) (PreH25 : (pmem_pre = pe)) (PreH26 : (perr_pre = error_addr)) (PreH27 : (mem_get_profile sg )) (PreH28 : (mem_get_call_domain critical sg invocation view pe before )) (PreH29 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pblk" ) )) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemGet_safety_wit_5 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 )) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH6 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH11 : (retval >= 0)) (PreH12 : (pe <> 0)) (PreH13 : (mem_get_profile sg )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (mem_get_access_matches sg view pe entry_2 access )) (PreH18 : (critical_region_interval critical sg invocation before entry )) (PreH19 : (UCOS2_state_inv sg entry )) (PreH20 : (interrupt_saved_value mask retval )) (PreH21 : (pmem_pre <> 0)) (PreH22 : (pmem_pre = pe)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (mem_get_profile sg )) (PreH25 : (mem_get_call_domain critical sg invocation view pe before )) (PreH26 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemGet_safety_wit_6 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 )) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH6 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH11 : (retval >= 0)) (PreH12 : (pe <> 0)) (PreH13 : (mem_get_profile sg )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (mem_get_access_matches sg view pe entry_2 access )) (PreH18 : (critical_region_interval critical sg invocation before entry )) (PreH19 : (UCOS2_state_inv sg entry )) (PreH20 : (interrupt_saved_value mask retval )) (PreH21 : (pmem_pre <> 0)) (PreH22 : (pmem_pre = pe)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (mem_get_profile sg )) (PreH25 : (mem_get_call_domain critical sg invocation view pe before )) (PreH26 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 93)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemGet_entail_wit_1 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : (pe <> 0)) (PreH2 : (mem_get_profile sg )) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (UCOS2_state_inv sg entry_2 )) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (mem_get_access_matches sg view pe entry_2 access )) (PreH7 : (critical_region_interval critical sg invocation before entry )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (interrupt_saved_value mask retval )) (PreH10 : (pmem_pre <> 0)) (PreH11 : (pmem_pre = pe)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (mem_get_profile sg )) (PreH14 : (mem_get_call_domain critical sg invocation view pe before )) (PreH15 : (mem_get_safe critical sg invocation view pe before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry_2 access )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry_2 access ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry_2 access )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_return_wit_1 := 
(
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 )) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH6 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH11 : (retval >= 0)) (PreH12 : (pe <> 0)) (PreH13 : (mem_get_profile sg )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (mem_get_access_matches sg view pe entry_2 access )) (PreH18 : (critical_region_interval critical sg invocation before entry )) (PreH19 : (UCOS2_state_inv sg entry )) (PreH20 : (interrupt_saved_value mask retval )) (PreH21 : (pmem_pre <> 0)) (PreH22 : (pmem_pre = pe)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (mem_get_profile sg )) (PreH25 : (mem_get_call_domain critical sg invocation view pe before )) (PreH26 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((perr_pre) # UChar  |-> 93)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before 0 X )
) \/
(
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 )) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH6 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH11 : (retval >= 0)) (PreH12 : (pe <> 0)) (PreH13 : (mem_get_profile sg )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (mem_get_access_matches sg view pe entry_2 access )) (PreH18 : (critical_region_interval critical sg invocation before entry )) (PreH19 : (UCOS2_state_inv sg entry )) (PreH20 : (interrupt_saved_value mask retval )) (PreH21 : (pmem_pre <> 0)) (PreH22 : (pmem_pre = pe)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (mem_get_profile sg )) (PreH25 : (mem_get_call_domain critical sg invocation view pe before )) (PreH26 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((perr_pre) # UChar  |-> 93)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before 0 X )
).

Definition OSMemGet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 )) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH6 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH11 : (retval >= 0)) (PreH12 : (pe <> 0)) (PreH13 : (mem_get_profile sg )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (mem_get_access_matches sg view pe entry_2 access )) (PreH18 : (critical_region_interval critical sg invocation before entry )) (PreH19 : (UCOS2_state_inv sg entry )) (PreH20 : (interrupt_saved_value mask retval )) (PreH21 : (pmem_pre <> 0)) (PreH22 : (pmem_pre = pe)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (mem_get_profile sg )) (PreH25 : (mem_get_call_domain critical sg invocation view pe before )) (PreH26 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((perr_pre) # UChar  |-> 93)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before 0 X )
.

Definition OSMemGet_return_wit_2 := 
(
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_get_access_checkpoint (entry_2) (access)) current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : ((memImageFree ((mem_get_access_image (access)))) = (mem_get_pointer ((mem_get_access_outcome (access)))))) (PreH5 : ((mem_get_error ((mem_get_access_outcome (access)))) = 0)) (PreH6 : (mem_get_protected sg view pe entry_2 (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry_2) (access)) )) (PreH7 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (mem_get_profile sg )) (PreH17 : (critical_region_interval critical sg invocation before entry_2 )) (PreH18 : (UCOS2_state_inv sg entry_2 )) (PreH19 : (interrupt_saved_value mask retval )) (PreH20 : (mem_get_access_matches sg view pe entry_2 access )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (UCOS2_state_inv sg entry )) (PreH23 : (interrupt_saved_value mask retval )) (PreH24 : (pmem_pre <> 0)) (PreH25 : (pmem_pre = pe)) (PreH26 : (perr_pre = error_addr)) (PreH27 : (mem_get_profile sg )) (PreH28 : (mem_get_call_domain critical sg invocation view pe before )) (PreH29 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before (memImageFree ((mem_get_access_image (access)))) X )
) \/
(
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_get_access_checkpoint (entry_2) (access)) current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : ((memImageFree ((mem_get_access_image (access)))) = (mem_get_pointer ((mem_get_access_outcome (access)))))) (PreH5 : ((mem_get_error ((mem_get_access_outcome (access)))) = 0)) (PreH6 : (mem_get_protected sg view pe entry_2 (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry_2) (access)) )) (PreH7 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (mem_get_profile sg )) (PreH17 : (critical_region_interval critical sg invocation before entry_2 )) (PreH18 : (UCOS2_state_inv sg entry_2 )) (PreH19 : (interrupt_saved_value mask retval )) (PreH20 : (mem_get_access_matches sg view pe entry_2 access )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (UCOS2_state_inv sg entry )) (PreH23 : (interrupt_saved_value mask retval )) (PreH24 : (pmem_pre <> 0)) (PreH25 : (pmem_pre = pe)) (PreH26 : (perr_pre = error_addr)) (PreH27 : (mem_get_profile sg )) (PreH28 : (mem_get_call_domain critical sg invocation view pe before )) (PreH29 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before (memImageFree ((mem_get_access_image (access)))) X )
).

Definition OSMemGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_get_access_checkpoint (entry_2) (access)) current )) (PreH2 : (pe <> 0)) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : ((memImageFree ((mem_get_access_image (access)))) = (mem_get_pointer ((mem_get_access_outcome (access)))))) (PreH5 : ((mem_get_error ((mem_get_access_outcome (access)))) = 0)) (PreH6 : (mem_get_protected sg view pe entry_2 (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry_2) (access)) )) (PreH7 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (mem_get_profile sg )) (PreH17 : (critical_region_interval critical sg invocation before entry_2 )) (PreH18 : (UCOS2_state_inv sg entry_2 )) (PreH19 : (interrupt_saved_value mask retval )) (PreH20 : (mem_get_access_matches sg view pe entry_2 access )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (UCOS2_state_inv sg entry )) (PreH23 : (interrupt_saved_value mask retval )) (PreH24 : (pmem_pre <> 0)) (PreH25 : (pmem_pre = pe)) (PreH26 : (perr_pre = error_addr)) (PreH27 : (mem_get_profile sg )) (PreH28 : (mem_get_call_domain critical sg invocation view pe before )) (PreH29 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before (memImageFree ((mem_get_access_image (access)))) X )
.

Definition OSMemGet_return_wit_3 := 
(
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_get_profile sg )) (PreH5 : (mem_get_call_domain critical sg invocation view pe before )) (PreH6 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |-> 96)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before 0 X )
) \/
(
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_get_profile sg )) (PreH5 : (mem_get_call_domain critical sg invocation view pe before )) (PreH6 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |-> 96)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before 0 X )
).

Definition OSMemGet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_get_profile sg )) (PreH5 : (mem_get_call_domain critical sg invocation view pe before )) (PreH6 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |-> 96)
|--
  (mem_get_api_post platform critical sg invocation origin mask view pe error_addr before 0 X )
.

Definition OSMemGet_partial_solve_wit_1 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_get_profile sg )) (PreH5 : (mem_get_call_domain critical sg invocation view pe before )) (PreH6 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (pmem_pre <> 0)) (PreH5 : (pmem_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (mem_get_profile sg )) (PreH8 : (mem_get_call_domain critical sg invocation view pe before )) (PreH9 : (mem_get_safe critical sg invocation view pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ”
.

Definition OSMemGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (pmem_pre <> 0)) (PreH5 : (pmem_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (mem_get_profile sg )) (PreH8 : (mem_get_call_domain critical sg invocation view pe before )) (PreH9 : (mem_get_safe critical sg invocation view pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_get_input_resources sg view pe )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_partial_solve_wit_2 := OSMemGet_partial_solve_wit_2_pure -> OSMemGet_partial_solve_wit_2_aux.

Definition OSMemGet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH2 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH3 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH4 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (pe <> 0)) (PreH9 : (mem_get_profile sg )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (UCOS2_state_inv sg entry_2 )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_get_access_matches sg view pe entry_2 access )) (PreH14 : (critical_region_interval critical sg invocation before entry )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (pmem_pre <> 0)) (PreH18 : (pmem_pre = pe)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (mem_get_profile sg )) (PreH21 : (mem_get_call_domain critical sg invocation view pe before )) (PreH22 : (mem_get_safe critical sg invocation view pe before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry_2 access )
  **  ((( &( "pblk" ) )) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((memImageFree ((mem_get_access_image (access)))) = (memImageFree ((mem_get_access_image (access))))) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ”
.

Definition OSMemGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH2 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH3 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH4 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (pe <> 0)) (PreH9 : (mem_get_profile sg )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (UCOS2_state_inv sg entry_2 )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_get_access_matches sg view pe entry_2 access )) (PreH14 : (critical_region_interval critical sg invocation before entry )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (pmem_pre <> 0)) (PreH18 : (pmem_pre = pe)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (mem_get_profile sg )) (PreH21 : (mem_get_call_domain critical sg invocation view pe before )) (PreH22 : (mem_get_safe critical sg invocation view pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry_2 access )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((memImageFree ((mem_get_access_image (access)))) = (memImageFree ((mem_get_access_image (access))))) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) > 0) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry_2 access ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  (mem_get_control_frame sg pe entry_2 access )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_partial_solve_wit_3 := OSMemGet_partial_solve_wit_3_pure -> OSMemGet_partial_solve_wit_3_aux.

Definition OSMemGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : ((memImageFree ((mem_get_access_image (access)))) = (memImageFree ((mem_get_access_image (access)))))) (PreH2 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH3 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH4 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (pe <> 0)) (PreH11 : (mem_get_profile sg )) (PreH12 : (critical_region_interval critical sg invocation before entry )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (mem_get_access_matches sg view pe entry access )) (PreH16 : (critical_region_interval critical sg invocation before entry_2 )) (PreH17 : (UCOS2_state_inv sg entry_2 )) (PreH18 : (interrupt_saved_value mask retval )) (PreH19 : (pmem_pre <> 0)) (PreH20 : (pmem_pre = pe)) (PreH21 : (perr_pre = error_addr)) (PreH22 : (mem_get_profile sg )) (PreH23 : (mem_get_call_domain critical sg invocation view pe before )) (PreH24 : (mem_get_safe critical sg invocation view pe before X )) ,
  ((( &( "pblk" ) )) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  (((memImageFree ((mem_get_access_image (access))))) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ” 
  &&  “ ((memImageFree ((mem_get_access_image (access)))) = (memImageFree ((mem_get_access_image (access))))) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ”
.

Definition OSMemGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : ((memImageFree ((mem_get_access_image (access)))) = (memImageFree ((mem_get_access_image (access)))))) (PreH2 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH3 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH4 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH5 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (pe <> 0)) (PreH11 : (mem_get_profile sg )) (PreH12 : (critical_region_interval critical sg invocation before entry )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (mem_get_access_matches sg view pe entry access )) (PreH16 : (critical_region_interval critical sg invocation before entry_2 )) (PreH17 : (UCOS2_state_inv sg entry_2 )) (PreH18 : (interrupt_saved_value mask retval )) (PreH19 : (pmem_pre <> 0)) (PreH20 : (pmem_pre = pe)) (PreH21 : (perr_pre = error_addr)) (PreH22 : (mem_get_profile sg )) (PreH23 : (mem_get_call_domain critical sg invocation view pe before )) (PreH24 : (mem_get_safe critical sg invocation view pe before X )) ,
  (((memImageFree ((mem_get_access_image (access))))) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ” 
  &&  “ ((memImageFree ((mem_get_access_image (access)))) = (memImageFree ((mem_get_access_image (access))))) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) > 0) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  (((memImageFree ((mem_get_access_image (access))))) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_partial_solve_wit_4 := OSMemGet_partial_solve_wit_4_pure -> OSMemGet_partial_solve_wit_4_aux.

Definition OSMemGet_partial_solve_wit_5 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : (pe <> 0)) (PreH2 : (critical_region_interval critical sg invocation before entry_2 )) (PreH3 : ((memImageFree ((mem_get_access_image (access)))) = (mem_get_pointer ((mem_get_access_outcome (access)))))) (PreH4 : ((mem_get_error ((mem_get_access_outcome (access)))) = 0)) (PreH5 : (mem_get_protected sg view pe entry_2 (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry_2) (access)) )) (PreH6 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) > 0)) (PreH8 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH9 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH13 : (retval >= 0)) (PreH14 : (pe <> 0)) (PreH15 : (mem_get_profile sg )) (PreH16 : (critical_region_interval critical sg invocation before entry_2 )) (PreH17 : (UCOS2_state_inv sg entry_2 )) (PreH18 : (interrupt_saved_value mask retval )) (PreH19 : (mem_get_access_matches sg view pe entry_2 access )) (PreH20 : (critical_region_interval critical sg invocation before entry )) (PreH21 : (UCOS2_state_inv sg entry )) (PreH22 : (interrupt_saved_value mask retval )) (PreH23 : (pmem_pre <> 0)) (PreH24 : (pmem_pre = pe)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (mem_get_profile sg )) (PreH27 : (mem_get_call_domain critical sg invocation view pe before )) (PreH28 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 (mem_get_access_checkpoint (entry_2) (access)) )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ ((memImageFree ((mem_get_access_image (access)))) = (mem_get_pointer ((mem_get_access_outcome (access))))) ” 
  &&  “ ((mem_get_error ((mem_get_access_outcome (access)))) = 0) ” 
  &&  “ (mem_get_protected sg view pe entry_2 (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry_2) (access)) ) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) > 0) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry_2 access ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 (mem_get_access_checkpoint (entry_2) (access)) )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH2 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH3 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH4 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (pe <> 0)) (PreH9 : (mem_get_profile sg )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_get_access_matches sg view pe entry access )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (pmem_pre <> 0)) (PreH18 : (pmem_pre = pe)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (mem_get_profile sg )) (PreH21 : (mem_get_call_domain critical sg invocation view pe before )) (PreH22 : (mem_get_safe critical sg invocation view pe before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= 0) ”
.

Definition OSMemGet_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH2 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH3 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH4 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (pe <> 0)) (PreH9 : (mem_get_profile sg )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_get_access_matches sg view pe entry access )) (PreH14 : (critical_region_interval critical sg invocation before entry_2 )) (PreH15 : (UCOS2_state_inv sg entry_2 )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (pmem_pre <> 0)) (PreH18 : (pmem_pre = pe)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (mem_get_profile sg )) (PreH21 : (mem_get_call_domain critical sg invocation view pe before )) (PreH22 : (mem_get_safe critical sg invocation view pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= 0) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= 0) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_partial_solve_wit_6 := OSMemGet_partial_solve_wit_6_pure -> OSMemGet_partial_solve_wit_6_aux.

Definition OSMemGet_partial_solve_wit_7 := 
forall (perr_pre: Z) (pmem_pre: Z) (X: (MemGetOutcome -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (access: MemGetAccess) (PreH1 : (pe <> 0)) (PreH2 : (critical_region_interval critical sg invocation before entry_2 )) (PreH3 : (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 )) (PreH4 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) (PreH5 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH6 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH7 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH8 : (retval <= UINT_MAX)) (PreH9 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (pe <> 0)) (PreH12 : (mem_get_profile sg )) (PreH13 : (critical_region_interval critical sg invocation before entry_2 )) (PreH14 : (UCOS2_state_inv sg entry_2 )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (mem_get_access_matches sg view pe entry_2 access )) (PreH17 : (critical_region_interval critical sg invocation before entry )) (PreH18 : (UCOS2_state_inv sg entry )) (PreH19 : (interrupt_saved_value mask retval )) (PreH20 : (pmem_pre <> 0)) (PreH21 : (pmem_pre = pe)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (mem_get_profile sg )) (PreH24 : (mem_get_call_domain critical sg invocation view pe before )) (PreH25 : (mem_get_safe critical sg invocation view pe before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 entry_2 )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (mem_get_protected sg view pe entry_2 mem_get_empty_outcome entry_2 ) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= 0) ” 
  &&  “ (0 <= (memImageNFree ((mem_get_access_image (access))))) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((memImageNFree ((mem_get_access_image (access)))) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_get_access_matches sg view pe entry_2 access ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (mem_get_call_domain critical sg invocation view pe before ) ” 
  &&  “ (mem_get_safe critical sg invocation view pe before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 entry_2 )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemGet_which_implies_wit_1 := 
(
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mem_get_profile sg )) (PreH3 : (mem_get_call_domain critical sg invocation view pe before )) (PreH4 : (critical_region_interval critical sg invocation before entry_2 )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (mem_get_input_resources sg view pe )
|--
  EX (access: MemGetAccess)  (entry: UCOS2_Verify_State) ,
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
) \/
(
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mem_get_profile sg )) (PreH3 : (mem_get_call_domain critical sg invocation view pe before )) (PreH4 : (critical_region_interval critical sg invocation before entry_2 )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (mem_get_input_resources sg view pe )
|--
  EX (access: MemGetAccess)  (entry: UCOS2_Verify_State) ,
  “ (pe <> 0) ” 
  &&  “ (mem_get_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (mem_get_access_matches sg view pe entry access ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
).

Definition OSMemGet_which_implies_wit_2 := 
(
forall (pe: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (access: MemGetAccess) (pblk: Z) (PreH1 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH2 : (0 < (memImageNFree ((mem_get_access_image (access)))))) ,
  (mem_get_control_frame sg pe entry access )
|--
  “ (pblk = (memImageFree ((mem_get_access_image (access))))) ” 
  &&  “ (0 < (memImageNFree ((mem_get_access_image (access))))) ”
  &&  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
) \/
(
forall (pe: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (access: MemGetAccess) (pblk: Z) (PreH1 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH2 : (0 < (memImageNFree ((mem_get_access_image (access)))))) ,
  (mem_get_control_frame sg pe entry access )
|--
  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
).

Definition OSMemGet_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (access: MemGetAccess) (pblk: Z) (PreH1 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH2 : (0 < (memImageNFree ((mem_get_access_image (access)))))) ,
  (mem_get_control_frame sg pe entry access )
|--
  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
.

Definition OSMemGet_which_implies_wit_3 := 
(
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (pblk: Z) (PreH1 : (pe <> 0)) (PreH2 : (mem_get_profile sg )) (PreH3 : (critical_region_interval critical sg invocation before entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (mem_get_access_matches sg view pe entry access )) (PreH7 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH8 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH9 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
|--
  “ (pe <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (pblk = (mem_get_pointer ((mem_get_access_outcome (access))))) ” 
  &&  “ ((mem_get_error ((mem_get_access_outcome (access)))) = 0) ” 
  &&  “ (mem_get_protected sg view pe entry (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry) (access)) ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (mem_get_access_checkpoint (entry) (access)) )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
) \/
(
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (pblk: Z) (PreH1 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH10 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
|--
  “ (mem_get_protected sg view pe entry (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry) (access)) ) ” 
  &&  “ ((mem_get_error ((mem_get_access_outcome (access)))) = 0) ” 
  &&  “ (pblk = (mem_get_pointer ((mem_get_access_outcome (access))))) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (mem_get_access_checkpoint (entry) (access)) )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
).

Definition OSMemGet_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (pblk: Z) (PreH1 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH10 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
|--
  “ (mem_get_protected sg view pe entry (mem_get_access_outcome (access)) (mem_get_access_checkpoint (entry) (access)) ) ”
.

Definition OSMemGet_which_implies_wit_3_split_goal_2 := 
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (pblk: Z) (PreH1 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH10 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
|--
  “ ((mem_get_error ((mem_get_access_outcome (access)))) = 0) ”
.

Definition OSMemGet_which_implies_wit_3_split_goal_3 := 
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (pblk: Z) (PreH1 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH10 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
|--
  “ (pblk = (mem_get_pointer ((mem_get_access_outcome (access))))) ”
.

Definition OSMemGet_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (pblk: Z) (PreH1 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_get_access_image (access)))) - 1 ) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (pblk = (memImageFree ((mem_get_access_image (access)))))) (PreH10 : (0 < (memImageNFree ((mem_get_access_image (access)))))) (PreH11 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (mem_get_access_next (access)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_get_access_image (access)))) - 1 ))
  **  ((pblk) # Ptr  |-> (mem_get_access_next (access)))
  **  (mem_get_success_frame sg pe entry access )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (mem_get_access_checkpoint (entry) (access)) )
  **  (mem_get_outcome_resources sg view pe (mem_get_access_outcome (access)) )
.

Definition OSMemGet_which_implies_wit_4 := 
(
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mem_get_profile sg )) (PreH3 : (critical_region_interval critical sg invocation before entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (mem_get_access_matches sg view pe entry access )) (PreH7 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH8 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
|--
  “ (pe <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_get_protected sg view pe entry mem_get_empty_outcome entry ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
) \/
(
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
|--
  “ (mem_get_protected sg view pe entry mem_get_empty_outcome entry ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
).

Definition OSMemGet_which_implies_wit_4_split_goal_1 := 
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
|--
  “ (mem_get_protected sg view pe entry mem_get_empty_outcome entry ) ”
.

Definition OSMemGet_which_implies_wit_4_split_goal_spatial := 
forall (pe: Z) (view: MemGetView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (access: MemGetAccess) (cpu_sr: Z) (PreH1 : ((memImageNFree ((mem_get_access_image (access)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_get_access_image (access)))) >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (mem_get_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (mem_get_access_matches sg view pe entry access )) (PreH9 : (0 <= (memImageNFree ((mem_get_access_image (access)))))) (PreH10 : ((memImageNFree ((mem_get_access_image (access)))) <= 0)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_get_access_image (access)))))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_get_access_image (access)))))
  **  (mem_get_control_frame sg pe entry access )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
  **  (mem_get_outcome_resources sg view pe mem_get_empty_outcome )
.

Module Type VC_Correct.


Axiom proof_of_OSMemGet_safety_wit_1 : OSMemGet_safety_wit_1.
Axiom proof_of_OSMemGet_safety_wit_2 : OSMemGet_safety_wit_2.
Axiom proof_of_OSMemGet_safety_wit_3 : OSMemGet_safety_wit_3.
Axiom proof_of_OSMemGet_safety_wit_4 : OSMemGet_safety_wit_4.
Axiom proof_of_OSMemGet_safety_wit_5 : OSMemGet_safety_wit_5.
Axiom proof_of_OSMemGet_safety_wit_6 : OSMemGet_safety_wit_6.
Axiom proof_of_OSMemGet_entail_wit_1 : OSMemGet_entail_wit_1.
Axiom proof_of_OSMemGet_return_wit_1 : OSMemGet_return_wit_1.
Axiom proof_of_OSMemGet_return_wit_2 : OSMemGet_return_wit_2.
Axiom proof_of_OSMemGet_return_wit_3 : OSMemGet_return_wit_3.
Axiom proof_of_OSMemGet_partial_solve_wit_1 : OSMemGet_partial_solve_wit_1.
Axiom proof_of_OSMemGet_partial_solve_wit_2_pure : OSMemGet_partial_solve_wit_2_pure.
Axiom proof_of_OSMemGet_partial_solve_wit_2 : OSMemGet_partial_solve_wit_2.
Axiom proof_of_OSMemGet_partial_solve_wit_3_pure : OSMemGet_partial_solve_wit_3_pure.
Axiom proof_of_OSMemGet_partial_solve_wit_3 : OSMemGet_partial_solve_wit_3.
Axiom proof_of_OSMemGet_partial_solve_wit_4_pure : OSMemGet_partial_solve_wit_4_pure.
Axiom proof_of_OSMemGet_partial_solve_wit_4 : OSMemGet_partial_solve_wit_4.
Axiom proof_of_OSMemGet_partial_solve_wit_5 : OSMemGet_partial_solve_wit_5.
Axiom proof_of_OSMemGet_partial_solve_wit_6_pure : OSMemGet_partial_solve_wit_6_pure.
Axiom proof_of_OSMemGet_partial_solve_wit_6 : OSMemGet_partial_solve_wit_6.
Axiom proof_of_OSMemGet_partial_solve_wit_7 : OSMemGet_partial_solve_wit_7.
Axiom proof_of_OSMemGet_which_implies_wit_1 : OSMemGet_which_implies_wit_1.
Axiom proof_of_OSMemGet_which_implies_wit_2 : OSMemGet_which_implies_wit_2.
Axiom proof_of_OSMemGet_which_implies_wit_3 : OSMemGet_which_implies_wit_3.
Axiom proof_of_OSMemGet_which_implies_wit_4 : OSMemGet_which_implies_wit_4.

End VC_Correct.
