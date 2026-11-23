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
Require Import Ucos2Verify.VC.code.memory.spec.mem_query_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMemQuery -----*)

Definition OSMemQuery_safety_wit_1 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (p_mem_data_pre = pd)) (PreH3 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH4 : (pmem_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_safety_wit_2 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (p_mem_data_pre = pd)) (PreH3 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH4 : (pmem_pre <> 0)) (PreH5 : (p_mem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_safety_wit_3 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (p_mem_data_pre = pd)) (PreH3 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH4 : (pmem_pre <> 0)) (PreH5 : (p_mem_data_pre <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_safety_wit_4 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMemQuery_safety_wit_5 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (p_mem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMemQuery_safety_wit_6 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (p_mem_data_pre <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ False ”
.

Definition OSMemQuery_safety_wit_7 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (p_mem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_safety_wit_8 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (p_mem_data_pre <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_safety_wit_9 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (p_mem_data_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMemQuery_safety_wit_10 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mem_data_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ False ”
.

Definition OSMemQuery_safety_wit_11 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (p_mem_data_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre <> 0)) ,
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_safety_wit_12 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : (p_mem_data_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pmem_pre = pe)) (PreH8 : (p_mem_data_pre = pd)) (PreH9 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH10 : (pmem_pre <> 0)) (PreH11 : (p_mem_data_pre <> 0)) ,
  (mem_query_restore_post platform critical sg invocation origin retval entry )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemQuery_return_wit_1 := 
(
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : (p_mem_data_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pmem_pre = pe)) (PreH8 : (p_mem_data_pre = pd)) (PreH9 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH10 : (pmem_pre <> 0)) (PreH11 : (p_mem_data_pre <> 0)) ,
  (mem_query_restore_post platform critical sg invocation origin retval entry )
  **  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |-> (unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)))
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 0 X )
  **  (caller_frame )
) \/
(
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : ((unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)) <= UINT_MAX)) (PreH2 : ((memImageNFree (image)) <= UINT_MAX)) (PreH3 : ((memImageCount (image)) <= UINT_MAX)) (PreH4 : ((memImageSize (image)) <= UINT_MAX)) (PreH5 : ((unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)) >= 0)) (PreH6 : ((memImageNFree (image)) >= 0)) (PreH7 : ((memImageCount (image)) >= 0)) (PreH8 : ((memImageSize (image)) >= 0)) (PreH9 : (pe <> 0)) (PreH10 : (pd <> 0)) (PreH11 : (pe <> 0)) (PreH12 : (pd <> 0)) (PreH13 : (p_mem_data_pre <> 0)) (PreH14 : (pmem_pre <> 0)) (PreH15 : (pmem_pre = pe)) (PreH16 : (p_mem_data_pre = pd)) (PreH17 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH18 : (pmem_pre <> 0)) (PreH19 : (p_mem_data_pre <> 0)) ,
  (mem_query_restore_post platform critical sg invocation origin retval entry )
  **  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |-> (unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)))
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 0 X )
  **  (caller_frame )
).

Definition OSMemQuery_return_wit_1_split_goal_spatial := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : ((unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)) <= UINT_MAX)) (PreH2 : ((memImageNFree (image)) <= UINT_MAX)) (PreH3 : ((memImageCount (image)) <= UINT_MAX)) (PreH4 : ((memImageSize (image)) <= UINT_MAX)) (PreH5 : ((unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)) >= 0)) (PreH6 : ((memImageNFree (image)) >= 0)) (PreH7 : ((memImageCount (image)) >= 0)) (PreH8 : ((memImageSize (image)) >= 0)) (PreH9 : (pe <> 0)) (PreH10 : (pd <> 0)) (PreH11 : (pe <> 0)) (PreH12 : (pd <> 0)) (PreH13 : (p_mem_data_pre <> 0)) (PreH14 : (pmem_pre <> 0)) (PreH15 : (pmem_pre = pe)) (PreH16 : (p_mem_data_pre = pd)) (PreH17 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH18 : (pmem_pre <> 0)) (PreH19 : (p_mem_data_pre <> 0)) ,
  (mem_query_restore_post platform critical sg invocation origin retval entry )
  **  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |-> (unsigned_last_nbits (((memImageCount (image)) - (memImageNFree (image)) )) (32)))
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 0 X )
  **  (caller_frame )
.

Definition OSMemQuery_return_wit_2 := 
(
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mem_data_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre = 0)) ,
  (caller_frame )
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 97 X )
  **  (caller_frame )
) \/
(
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mem_data_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre = 0)) ,
  (caller_frame )
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 97 X )
  **  (caller_frame )
).

Definition OSMemQuery_return_wit_2_split_goal_spatial := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mem_data_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre = 0)) ,
  (caller_frame )
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 97 X )
  **  (caller_frame )
.

Definition OSMemQuery_return_wit_3 := 
(
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre = 0)) ,
  (caller_frame )
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 96 X )
  **  (caller_frame )
) \/
(
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre = 0)) ,
  (caller_frame )
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 96 X )
  **  (caller_frame )
).

Definition OSMemQuery_return_wit_3_split_goal_spatial := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (p_mem_data_pre = pd)) (PreH4 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH5 : (pmem_pre = 0)) ,
  (caller_frame )
|--
  (mem_query_api_post platform critical sg invocation origin mask view pe pd before 96 X )
  **  (caller_frame )
.

Definition OSMemQuery_partial_solve_wit_1 := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mem_data_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre <> 0)) ,
  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (p_mem_data_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (p_mem_data_pre = pd) ” 
  &&  “ (mem_query_safe critical sg invocation view pe pd before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
.

Definition OSMemQuery_partial_solve_wit_2_pure := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (p_mem_data_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre <> 0)) ,
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
.

Definition OSMemQuery_partial_solve_wit_2_aux := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (p_mem_data_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (p_mem_data_pre = pd)) (PreH5 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (p_mem_data_pre <> 0)) ,
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> p_mem_data_pre)
  **  (caller_frame )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (mem_query_source_rep sg pe view )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (p_mem_data_pre = pd) ” 
  &&  “ (mem_query_safe critical sg invocation view pe pd before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ”
  &&  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |->_)
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
.

Definition OSMemQuery_partial_solve_wit_2 := OSMemQuery_partial_solve_wit_2_pure -> OSMemQuery_partial_solve_wit_2_aux.

Definition OSMemQuery_partial_solve_wit_3_pure := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (p_mem_data_pre <> 0)) (PreH4 : (pmem_pre <> 0)) (PreH5 : (pmem_pre = pe)) (PreH6 : (p_mem_data_pre = pd)) (PreH7 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH8 : (pmem_pre <> 0)) (PreH9 : (p_mem_data_pre <> 0)) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mem_query_copy_frame platform critical sg invocation origin mask retval before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
.

Definition OSMemQuery_partial_solve_wit_3_aux := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (p_mem_data_pre <> 0)) (PreH4 : (pmem_pre <> 0)) (PreH5 : (pmem_pre = pe)) (PreH6 : (p_mem_data_pre = pd)) (PreH7 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH8 : (pmem_pre <> 0)) (PreH9 : (p_mem_data_pre <> 0)) ,
  (mem_query_copy_frame platform critical sg invocation origin mask retval before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (p_mem_data_pre = pd) ” 
  &&  “ (mem_query_safe critical sg invocation view pe pd before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ”
  &&  (mem_query_copy_frame platform critical sg invocation origin mask retval before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
.

Definition OSMemQuery_partial_solve_wit_3 := OSMemQuery_partial_solve_wit_3_pure -> OSMemQuery_partial_solve_wit_3_aux.

Definition OSMemQuery_partial_solve_wit_4_pure := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : (p_mem_data_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pmem_pre = pe)) (PreH8 : (p_mem_data_pre = pd)) (PreH9 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH10 : (pmem_pre <> 0)) (PreH11 : (p_mem_data_pre <> 0)) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMemQuery_partial_solve_wit_4_aux := 
forall (p_mem_data_pre: Z) (pmem_pre: Z) (X: (Z -> ((@option (@list Z)) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : (p_mem_data_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pmem_pre = pe)) (PreH8 : (p_mem_data_pre = pd)) (PreH9 : (mem_query_safe critical sg invocation view pe pd before X )) (PreH10 : (pmem_pre <> 0)) (PreH11 : (p_mem_data_pre <> 0)) ,
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (p_mem_data_pre = pd) ” 
  &&  “ (mem_query_safe critical sg invocation view pe pd before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (p_mem_data_pre <> 0) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (mem_query_source_rep sg pe view )
  **  (caller_frame )
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNFree")) # UInt  |-> (memImageNFree (image)))
  **  ((&((pd)  # "os_mem_data" ->ₛ "OSNUsed")) # UInt  |->_)
.

Definition OSMemQuery_partial_solve_wit_4 := OSMemQuery_partial_solve_wit_4_pure -> OSMemQuery_partial_solve_wit_4_aux.

Definition OSMemQuery_which_implies_wit_1 := 
(
forall (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) ,
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (mem_query_source_rep sg pe view )
|--
  EX (entry: UCOS2_Verify_State)  (image: MemoryControlImage) ,
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
  &&  (mem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
) \/
(
forall (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) ,
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (mem_query_admission (critical) (sg) (invocation) (pe) (view) (before)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (mem_query_source_rep sg pe view )
|--
  EX (entry: UCOS2_Verify_State)  (image: MemoryControlImage) ,
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
  &&  (mem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
).

Definition OSMemQuery_which_implies_wit_2 := 
(
forall (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) ,
  (mem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
  &&  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mem_query_source_rep sg pe view )
) \/
(
forall (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : ((memImageNFree (image)) <= UINT_MAX)) (PreH2 : ((memImageCount (image)) <= UINT_MAX)) (PreH3 : ((memImageSize (image)) <= UINT_MAX)) (PreH4 : ((memImageNFree (image)) >= 0)) (PreH5 : ((memImageCount (image)) >= 0)) (PreH6 : ((memImageSize (image)) >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pd <> 0)) ,
  (mem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
|--
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mem_query_source_rep sg pe view )
).

Definition OSMemQuery_which_implies_wit_2_split_goal_spatial := 
forall (pd: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : ((memImageNFree (image)) <= UINT_MAX)) (PreH2 : ((memImageCount (image)) <= UINT_MAX)) (PreH3 : ((memImageSize (image)) <= UINT_MAX)) (PreH4 : ((memImageNFree (image)) >= 0)) (PreH5 : ((memImageCount (image)) >= 0)) (PreH6 : ((memImageSize (image)) >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pd <> 0)) ,
  (mem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry view pe image )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount (image)))
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree (image)))
|--
  (coq_prop (mem_query_acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (mem_query_selected (view) (entry) (image)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mem_query_source_rep sg pe view )
.

Module Type VC_Correct.


Axiom proof_of_OSMemQuery_safety_wit_1 : OSMemQuery_safety_wit_1.
Axiom proof_of_OSMemQuery_safety_wit_2 : OSMemQuery_safety_wit_2.
Axiom proof_of_OSMemQuery_safety_wit_3 : OSMemQuery_safety_wit_3.
Axiom proof_of_OSMemQuery_safety_wit_4 : OSMemQuery_safety_wit_4.
Axiom proof_of_OSMemQuery_safety_wit_5 : OSMemQuery_safety_wit_5.
Axiom proof_of_OSMemQuery_safety_wit_6 : OSMemQuery_safety_wit_6.
Axiom proof_of_OSMemQuery_safety_wit_7 : OSMemQuery_safety_wit_7.
Axiom proof_of_OSMemQuery_safety_wit_8 : OSMemQuery_safety_wit_8.
Axiom proof_of_OSMemQuery_safety_wit_9 : OSMemQuery_safety_wit_9.
Axiom proof_of_OSMemQuery_safety_wit_10 : OSMemQuery_safety_wit_10.
Axiom proof_of_OSMemQuery_safety_wit_11 : OSMemQuery_safety_wit_11.
Axiom proof_of_OSMemQuery_safety_wit_12 : OSMemQuery_safety_wit_12.
Axiom proof_of_OSMemQuery_return_wit_1 : OSMemQuery_return_wit_1.
Axiom proof_of_OSMemQuery_return_wit_2 : OSMemQuery_return_wit_2.
Axiom proof_of_OSMemQuery_return_wit_3 : OSMemQuery_return_wit_3.
Axiom proof_of_OSMemQuery_partial_solve_wit_1 : OSMemQuery_partial_solve_wit_1.
Axiom proof_of_OSMemQuery_partial_solve_wit_2_pure : OSMemQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSMemQuery_partial_solve_wit_2 : OSMemQuery_partial_solve_wit_2.
Axiom proof_of_OSMemQuery_partial_solve_wit_3_pure : OSMemQuery_partial_solve_wit_3_pure.
Axiom proof_of_OSMemQuery_partial_solve_wit_3 : OSMemQuery_partial_solve_wit_3.
Axiom proof_of_OSMemQuery_partial_solve_wit_4_pure : OSMemQuery_partial_solve_wit_4_pure.
Axiom proof_of_OSMemQuery_partial_solve_wit_4 : OSMemQuery_partial_solve_wit_4.
Axiom proof_of_OSMemQuery_which_implies_wit_1 : OSMemQuery_which_implies_wit_1.
Axiom proof_of_OSMemQuery_which_implies_wit_2 : OSMemQuery_which_implies_wit_2.

End VC_Correct.
