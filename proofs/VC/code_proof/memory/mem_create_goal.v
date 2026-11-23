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
Require Import Ucos2Verify.VC.code.memory.spec.mem_create_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSMemCreate -----*)

Definition OSMemCreate_safety_wit_1 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_arguments_in_range base count size )) (PreH2 : (blksize_pre <= UINT_MAX)) (PreH3 : (nblks_pre <= UINT_MAX)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (blksize_pre >= 0)) (PreH6 : (nblks_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (addr_pre = base)) (PreH9 : (nblks_pre = count)) (PreH10 : (blksize_pre = size)) (PreH11 : (perr_pre = output)) (PreH12 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH13 : (mem_create_profile sg )) (PreH14 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH15 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH16 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH17 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_2 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = 0)) (PreH2 : (mem_create_arguments_in_range base count size )) (PreH3 : (blksize_pre <= UINT_MAX)) (PreH4 : (nblks_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (blksize_pre >= 0)) (PreH7 : (nblks_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (addr_pre = base)) (PreH10 : (nblks_pre = count)) (PreH11 : (blksize_pre = size)) (PreH12 : (perr_pre = output)) (PreH13 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH14 : (mem_create_profile sg )) (PreH15 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH16 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH17 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH18 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_3 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0)) (PreH2 : (addr_pre <> 0)) (PreH3 : (mem_create_arguments_in_range base count size )) (PreH4 : (blksize_pre <= UINT_MAX)) (PreH5 : (nblks_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (blksize_pre >= 0)) (PreH8 : (nblks_pre >= 0)) (PreH9 : (0 >= 0)) (PreH10 : (addr_pre = base)) (PreH11 : (nblks_pre = count)) (PreH12 : (blksize_pre = size)) (PreH13 : (perr_pre = output)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH17 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH18 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH19 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_4 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (nblks_pre < 2)) (PreH2 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH3 : (addr_pre <> 0)) (PreH4 : (mem_create_arguments_in_range base count size )) (PreH5 : (blksize_pre <= UINT_MAX)) (PreH6 : (nblks_pre <= UINT_MAX)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (blksize_pre >= 0)) (PreH9 : (nblks_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (addr_pre = base)) (PreH12 : (nblks_pre = count)) (PreH13 : (blksize_pre = size)) (PreH14 : (perr_pre = output)) (PreH15 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH16 : (mem_create_profile sg )) (PreH17 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 91)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_5 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre < sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 92)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_6 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (mem_create_arguments_valid base count size )) (PreH5 : (blksize_pre >= sizeof(PTR))) (PreH6 : (nblks_pre >= 2)) (PreH7 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH8 : (addr_pre <> 0)) (PreH9 : (mem_create_arguments_in_range base count size )) (PreH10 : (blksize_pre <= UINT_MAX)) (PreH11 : (nblks_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (blksize_pre >= 0)) (PreH14 : (nblks_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (addr_pre = base)) (PreH17 : (nblks_pre = count)) (PreH18 : (blksize_pre = size)) (PreH19 : (perr_pre = output)) (PreH20 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH21 : (mem_create_profile sg )) (PreH22 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH23 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH24 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH25 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_7 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH2 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_arguments_valid base count size )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH10 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (critical_region_interval critical sg invocation before entry )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (mem_create_arguments_valid base count size )) (PreH16 : (blksize_pre >= sizeof(PTR))) (PreH17 : (nblks_pre >= 2)) (PreH18 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH19 : (addr_pre <> 0)) (PreH20 : (mem_create_arguments_in_range base count size )) (PreH21 : (blksize_pre <= UINT_MAX)) (PreH22 : (nblks_pre <= UINT_MAX)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (blksize_pre >= 0)) (PreH25 : (nblks_pre >= 0)) (PreH26 : (0 >= 0)) (PreH27 : (addr_pre = base)) (PreH28 : (nblks_pre = count)) (PreH29 : (blksize_pre = size)) (PreH30 : (perr_pre = output)) (PreH31 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH32 : (mem_create_profile sg )) (PreH33 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH34 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH35 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH36 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_8 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint current )) (PreH2 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH3 : (mem_create_profile sg )) (PreH4 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH5 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH6 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_9 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint current )) (PreH2 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH3 : (mem_create_profile sg )) (PreH4 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH5 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH6 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_10 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (0 = 0)) (PreH2 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (0) (90)) current )) (PreH3 : (pmem = 0)) (PreH4 : (critical_region_interval critical sg invocation checkpoint current )) (PreH5 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH8 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH9 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH10 : (mem_create_safe critical sg invocation base count size output before X )) (PreH11 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "pmem" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 90)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (current) (caller_frame)) output )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_safety_wit_11 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i = (count - 1 ))) (PreH2 : ((count - 1 ) = (count - 1 ))) (PreH3 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH6 : (mem_create_safe critical sg invocation base count size output before X )) (PreH7 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH8 : (i >= loops)) (PreH9 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH10 : (mode = MemCreateArena)) (PreH11 : ((memPrivateBase (private)) = base)) (PreH12 : ((memPrivateBlockCount (private)) = count)) (PreH13 : ((memPrivateBlockSize (private)) = size)) (PreH14 : (memory_private_initialization_valid private )) (PreH15 : (loops = (count - 1 ))) (PreH16 : (0 <= i)) (PreH17 : (i <= (count - 1 ))) (PreH18 : (pblk = (base + (i * size ) ))) (PreH19 : (plink = (base + (i * size ) ))) (PreH20 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH21 : (mode = MemCreateArena)) (PreH22 : ((memPrivateBase (private)) = base)) (PreH23 : ((memPrivateBlockCount (private)) = count)) (PreH24 : ((memPrivateBlockSize (private)) = size)) (PreH25 : (memory_private_initialization_valid private )) (PreH26 : (pmem <> 0)) (PreH27 : (critical_region_interval critical sg invocation checkpoint current )) (PreH28 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH29 : (mem_create_profile sg )) (PreH30 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH31 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH32 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH33 : (mem_create_safe critical sg invocation base count size output before X )) (PreH34 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "loops" ) )) # UInt  |-> (count - 1 ))
  **  ((( &( "plink" ) )) # Ptr  |-> (base + (i * size ) ))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((base + (i * size ) )) # Ptr  |->_)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemCreate_entail_wit_1 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = base)) (PreH2 : (nblks_pre = count)) (PreH3 : (blksize_pre = size)) (PreH4 : (perr_pre = output)) (PreH5 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH8 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH9 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH10 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (blksize_pre <= UINT_MAX)) (PreH2 : (nblks_pre <= UINT_MAX)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (blksize_pre >= 0)) (PreH5 : (nblks_pre >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (addr_pre = base)) (PreH8 : (nblks_pre = count)) (PreH9 : (blksize_pre = size)) (PreH10 : (perr_pre = output)) (PreH11 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH12 : (mem_create_profile sg )) (PreH13 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH14 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH15 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH16 : (mem_create_safe critical sg invocation base count size output before X )) ,
  TT && emp 
|--
  “ (mem_create_arguments_in_range addr_pre nblks_pre blksize_pre ) ”
  &&  emp
).

Definition OSMemCreate_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (blksize_pre <= UINT_MAX)) (PreH2 : (nblks_pre <= UINT_MAX)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (blksize_pre >= 0)) (PreH5 : (nblks_pre >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (addr_pre = base)) (PreH8 : (nblks_pre = count)) (PreH9 : (blksize_pre = size)) (PreH10 : (perr_pre = output)) (PreH11 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH12 : (mem_create_profile sg )) (PreH13 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH14 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH15 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH16 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (mem_create_arguments_in_range addr_pre nblks_pre blksize_pre )
.

Definition OSMemCreate_entail_wit_2 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre >= sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (blksize_pre >= sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (blksize_pre >= sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  TT && emp 
|--
  “ (mem_create_arguments_valid addr_pre nblks_pre blksize_pre ) ”
  &&  emp
).

Definition OSMemCreate_entail_wit_2_split_goal_1 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (blksize_pre >= sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (mem_create_arguments_valid addr_pre nblks_pre blksize_pre )
.

Definition OSMemCreate_entail_wit_3 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_arguments_valid base count size )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (mem_create_arguments_valid base count size )) (PreH12 : (blksize_pre >= sizeof(PTR))) (PreH13 : (nblks_pre >= 2)) (PreH14 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH15 : (addr_pre <> 0)) (PreH16 : (mem_create_arguments_in_range base count size )) (PreH17 : (blksize_pre <= UINT_MAX)) (PreH18 : (nblks_pre <= UINT_MAX)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (blksize_pre >= 0)) (PreH21 : (nblks_pre >= 0)) (PreH22 : (0 >= 0)) (PreH23 : (addr_pre = base)) (PreH24 : (nblks_pre = count)) (PreH25 : (blksize_pre = size)) (PreH26 : (perr_pre = output)) (PreH27 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH28 : (mem_create_profile sg )) (PreH29 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH30 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH31 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH32 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
|--
  “ (0 <= (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) < 4294967296) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (blksize_pre >= sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_arguments_valid base count size )) (PreH6 : (critical_region_interval critical sg invocation before entry )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_create_arguments_valid base count size )) (PreH14 : (blksize_pre >= sizeof(PTR))) (PreH15 : (nblks_pre >= 2)) (PreH16 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH17 : (addr_pre <> 0)) (PreH18 : (mem_create_arguments_in_range base count size )) (PreH19 : (blksize_pre <= UINT_MAX)) (PreH20 : (nblks_pre <= UINT_MAX)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (blksize_pre >= 0)) (PreH23 : (nblks_pre >= 0)) (PreH24 : (0 >= 0)) (PreH25 : (addr_pre = base)) (PreH26 : (nblks_pre = count)) (PreH27 : (blksize_pre = size)) (PreH28 : (perr_pre = output)) (PreH29 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH32 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH33 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) ,
  TT && emp 
|--
  “ ((mem_create_free_head (sg) (entry)) < 4294967296) ” 
  &&  “ (0 <= (mem_create_free_head (sg) (entry))) ”
  &&  emp
).

Definition OSMemCreate_entail_wit_3_split_goal_1 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_arguments_valid base count size )) (PreH6 : (critical_region_interval critical sg invocation before entry )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_create_arguments_valid base count size )) (PreH14 : (blksize_pre >= sizeof(PTR))) (PreH15 : (nblks_pre >= 2)) (PreH16 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH17 : (addr_pre <> 0)) (PreH18 : (mem_create_arguments_in_range base count size )) (PreH19 : (blksize_pre <= UINT_MAX)) (PreH20 : (nblks_pre <= UINT_MAX)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (blksize_pre >= 0)) (PreH23 : (nblks_pre >= 0)) (PreH24 : (0 >= 0)) (PreH25 : (addr_pre = base)) (PreH26 : (nblks_pre = count)) (PreH27 : (blksize_pre = size)) (PreH28 : (perr_pre = output)) (PreH29 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH32 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH33 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((mem_create_free_head (sg) (entry)) < 4294967296)
.

Definition OSMemCreate_entail_wit_3_split_goal_2 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_arguments_valid base count size )) (PreH6 : (critical_region_interval critical sg invocation before entry )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (mem_create_arguments_valid base count size )) (PreH14 : (blksize_pre >= sizeof(PTR))) (PreH15 : (nblks_pre >= 2)) (PreH16 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH17 : (addr_pre <> 0)) (PreH18 : (mem_create_arguments_in_range base count size )) (PreH19 : (blksize_pre <= UINT_MAX)) (PreH20 : (nblks_pre <= UINT_MAX)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (blksize_pre >= 0)) (PreH23 : (nblks_pre >= 0)) (PreH24 : (0 >= 0)) (PreH25 : (addr_pre = base)) (PreH26 : (nblks_pre = count)) (PreH27 : (blksize_pre = size)) (PreH28 : (perr_pre = output)) (PreH29 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH32 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH33 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (0 <= (mem_create_free_head (sg) (entry)))
.

Definition OSMemCreate_entail_wit_4_1 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (PreH1 : ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mem_create_reservation sg base count size entry private post )) (PreH3 : (UCOS2_state_inv sg (replace_MemoryS (post) (entry)) )) (PreH4 : (mem_create_byte_access (mem_create_detached_resources (sg) ((replace_MemoryS (post) (entry))) ((mem_create_selection (private))) (mode) (base) (count) (size) (caller_frame)) output )) (PreH5 : ((mem_create_free_head (sg) (entry)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH6 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH7 : (mem_create_profile sg )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (mode = MemCreateArena)) (PreH10 : (mem_create_arguments_valid base count size )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (mem_create_reservation sg base count size entry private post )) (PreH13 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH14 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH15 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH16 : (retval <= UINT_MAX)) (PreH17 : (retval >= 0)) (PreH18 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH19 : (mem_create_profile sg )) (PreH20 : (mem_create_arguments_valid base count size )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH23 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH24 : (UCOS2_state_inv sg entry )) (PreH25 : (critical_region_interval critical sg invocation before entry )) (PreH26 : (UCOS2_state_inv sg entry )) (PreH27 : (interrupt_saved_value mask retval )) (PreH28 : (mem_create_arguments_valid base count size )) (PreH29 : (blksize_pre >= sizeof(PTR))) (PreH30 : (nblks_pre >= 2)) (PreH31 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH32 : (addr_pre <> 0)) (PreH33 : (mem_create_arguments_in_range base count size )) (PreH34 : (blksize_pre <= UINT_MAX)) (PreH35 : (nblks_pre <= UINT_MAX)) (PreH36 : (0 <= UINT_MAX)) (PreH37 : (blksize_pre >= 0)) (PreH38 : (nblks_pre >= 0)) (PreH39 : (0 >= 0)) (PreH40 : (addr_pre = base)) (PreH41 : (nblks_pre = count)) (PreH42 : (blksize_pre = size)) (PreH43 : (perr_pre = output)) (PreH44 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH45 : (mem_create_profile sg )) (PreH46 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH47 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH48 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH49 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (UCOS2_inv sg (replace_MemoryS (post) (entry)) )
  **  (memory_private_control_rep sg private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
|--
  EX (checkpoint: UCOS2_Verify_State)  (selected: MemCreateSelection) ,
  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry checkpoint )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (PreH1 : (mem_create_reservation sg base count size entry private post )) (PreH2 : (UCOS2_state_inv sg (replace_MemoryS (post) (entry)) )) (PreH3 : (mem_create_byte_access (mem_create_detached_resources (sg) ((replace_MemoryS (post) (entry))) ((mem_create_selection (private))) (mode) (base) (count) (size) (caller_frame)) output )) (PreH4 : ((mem_create_free_head (sg) (entry)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH5 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH6 : (mem_create_profile sg )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (mode = MemCreateArena)) (PreH9 : (mem_create_arguments_valid base count size )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (mem_create_reservation sg base count size entry private post )) (PreH12 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH13 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH14 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH15 : (retval <= UINT_MAX)) (PreH16 : (retval >= 0)) (PreH17 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH18 : (mem_create_profile sg )) (PreH19 : (mem_create_arguments_valid base count size )) (PreH20 : (critical_region_interval critical sg invocation before entry )) (PreH21 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH22 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH23 : (UCOS2_state_inv sg entry )) (PreH24 : (critical_region_interval critical sg invocation before entry )) (PreH25 : (UCOS2_state_inv sg entry )) (PreH26 : (interrupt_saved_value mask retval )) (PreH27 : (mem_create_arguments_valid base count size )) (PreH28 : (blksize_pre >= sizeof(PTR))) (PreH29 : (nblks_pre >= 2)) (PreH30 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH31 : (addr_pre <> 0)) (PreH32 : (mem_create_arguments_in_range base count size )) (PreH33 : (blksize_pre <= UINT_MAX)) (PreH34 : (nblks_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (blksize_pre >= 0)) (PreH37 : (nblks_pre >= 0)) (PreH38 : (0 >= 0)) (PreH39 : (addr_pre = base)) (PreH40 : (nblks_pre = count)) (PreH41 : (blksize_pre = size)) (PreH42 : (perr_pre = output)) (PreH43 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH44 : (mem_create_profile sg )) (PreH45 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH46 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH47 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH48 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (UCOS2_inv sg (replace_MemoryS (post) (entry)) )
  **  (memory_private_control_rep sg private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  EX (checkpoint: UCOS2_Verify_State)  (selected: MemCreateSelection) ,
  “ (perr_pre = output) ” 
  &&  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry checkpoint )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
).

Definition OSMemCreate_entail_wit_4_2 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((mem_create_free_head (sg) (entry)) = 0)) (PreH2 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH3 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval >= 0)) (PreH6 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_arguments_valid base count size )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH11 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (mem_create_arguments_valid base count size )) (PreH17 : (blksize_pre >= sizeof(PTR))) (PreH18 : (nblks_pre >= 2)) (PreH19 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH20 : (addr_pre <> 0)) (PreH21 : (mem_create_arguments_in_range base count size )) (PreH22 : (blksize_pre <= UINT_MAX)) (PreH23 : (nblks_pre <= UINT_MAX)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (blksize_pre >= 0)) (PreH26 : (nblks_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (addr_pre = base)) (PreH29 : (nblks_pre = count)) (PreH30 : (blksize_pre = size)) (PreH31 : (perr_pre = output)) (PreH32 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH33 : (mem_create_profile sg )) (PreH34 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH35 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH36 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH37 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
|--
  EX (checkpoint: UCOS2_Verify_State)  (selected: MemCreateSelection) ,
  “ ((mem_create_free_head (sg) (entry)) = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry checkpoint )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((mem_create_free_head (sg) (entry)) = 0)) (PreH2 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH3 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval >= 0)) (PreH6 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_arguments_valid base count size )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH11 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (mem_create_arguments_valid base count size )) (PreH17 : (blksize_pre >= sizeof(PTR))) (PreH18 : (nblks_pre >= 2)) (PreH19 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH20 : (addr_pre <> 0)) (PreH21 : (mem_create_arguments_in_range base count size )) (PreH22 : (blksize_pre <= UINT_MAX)) (PreH23 : (nblks_pre <= UINT_MAX)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (blksize_pre >= 0)) (PreH26 : (nblks_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (addr_pre = base)) (PreH29 : (nblks_pre = count)) (PreH30 : (blksize_pre = size)) (PreH31 : (perr_pre = output)) (PreH32 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH33 : (mem_create_profile sg )) (PreH34 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH35 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH36 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH37 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  EX (checkpoint: UCOS2_Verify_State)  (selected: MemCreateSelection) ,
  “ (perr_pre = output) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry checkpoint )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
).

Definition OSMemCreate_entail_wit_5 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (PreH1 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mode = MemCreateArena)) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (pmem <> 0)) (PreH8 : (critical_region_interval critical sg invocation checkpoint current )) (PreH9 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH10 : (mem_create_profile sg )) (PreH11 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH12 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH13 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH14 : (mem_create_safe critical sg invocation base count size output before X )) (PreH15 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private 0 caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ ((unsigned_last_nbits ((count - 1 )) (32)) = (count - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (count - 1 )) ” 
  &&  “ (base = (base + (0 * size ) )) ” 
  &&  “ (base = (base + (0 * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private 0 caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (PreH1 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mode = MemCreateArena)) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (pmem <> 0)) (PreH8 : (critical_region_interval critical sg invocation checkpoint current )) (PreH9 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH10 : (mem_create_profile sg )) (PreH11 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH12 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH13 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH14 : (mem_create_safe critical sg invocation base count size output before X )) (PreH15 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  TT && emp 
|--
  “ (0 <= (count - 1 )) ” 
  &&  “ ((unsigned_last_nbits ((count - 1 )) (32)) = (count - 1 )) ”
  &&  emp
).

Definition OSMemCreate_entail_wit_5_split_goal_1 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (PreH1 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mode = MemCreateArena)) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (pmem <> 0)) (PreH8 : (critical_region_interval critical sg invocation checkpoint current )) (PreH9 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH10 : (mem_create_profile sg )) (PreH11 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH12 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH13 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH14 : (mem_create_safe critical sg invocation base count size output before X )) (PreH15 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (0 <= (count - 1 ))
.

Definition OSMemCreate_entail_wit_5_split_goal_2 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (PreH1 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mode = MemCreateArena)) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (pmem <> 0)) (PreH8 : (critical_region_interval critical sg invocation checkpoint current )) (PreH9 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH10 : (mem_create_profile sg )) (PreH11 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH12 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH13 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH14 : (mem_create_safe critical sg invocation base count size output before X )) (PreH15 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((unsigned_last_nbits ((count - 1 )) (32)) = (count - 1 ))
.

Definition OSMemCreate_entail_wit_6 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : ((base + (i * size ) ) = (base + (i * size ) ))) (PreH2 : ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) ))) (PreH3 : (0 <= i)) (PreH4 : (i < (count - 1 ))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output )) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mem_create_cursor_resources sg current private (i + 1 ) caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (count - 1 )) ” 
  &&  “ ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private (i + 1 ) caller_frame X )
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (count - 1 ))) (PreH3 : (mem_create_profile sg )) (PreH4 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH5 : (mem_create_safe critical sg invocation base count size output before X )) (PreH6 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output )) (PreH7 : (i < loops)) (PreH8 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH9 : (mode = MemCreateArena)) (PreH10 : ((memPrivateBase (private)) = base)) (PreH11 : ((memPrivateBlockCount (private)) = count)) (PreH12 : ((memPrivateBlockSize (private)) = size)) (PreH13 : (memory_private_initialization_valid private )) (PreH14 : (loops = (count - 1 ))) (PreH15 : (0 <= i)) (PreH16 : (i <= (count - 1 ))) (PreH17 : (pblk = (base + (i * size ) ))) (PreH18 : (plink = (base + (i * size ) ))) (PreH19 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH20 : (mode = MemCreateArena)) (PreH21 : ((memPrivateBase (private)) = base)) (PreH22 : ((memPrivateBlockCount (private)) = count)) (PreH23 : ((memPrivateBlockSize (private)) = size)) (PreH24 : (memory_private_initialization_valid private )) (PreH25 : (pmem <> 0)) (PreH26 : (critical_region_interval critical sg invocation checkpoint current )) (PreH27 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH28 : (mem_create_profile sg )) (PreH29 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH30 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH31 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH32 : (mem_create_safe critical sg invocation base count size output before X )) (PreH33 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mem_create_cursor_resources sg current private (i + 1 ) caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private (i + 1 ) caller_frame X )
).

Definition OSMemCreate_entail_wit_6_split_goal_spatial := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (count - 1 ))) (PreH3 : (mem_create_profile sg )) (PreH4 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH5 : (mem_create_safe critical sg invocation base count size output before X )) (PreH6 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output )) (PreH7 : (i < loops)) (PreH8 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH9 : (mode = MemCreateArena)) (PreH10 : ((memPrivateBase (private)) = base)) (PreH11 : ((memPrivateBlockCount (private)) = count)) (PreH12 : ((memPrivateBlockSize (private)) = size)) (PreH13 : (memory_private_initialization_valid private )) (PreH14 : (loops = (count - 1 ))) (PreH15 : (0 <= i)) (PreH16 : (i <= (count - 1 ))) (PreH17 : (pblk = (base + (i * size ) ))) (PreH18 : (plink = (base + (i * size ) ))) (PreH19 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH20 : (mode = MemCreateArena)) (PreH21 : ((memPrivateBase (private)) = base)) (PreH22 : ((memPrivateBlockCount (private)) = count)) (PreH23 : ((memPrivateBlockSize (private)) = size)) (PreH24 : (memory_private_initialization_valid private )) (PreH25 : (pmem <> 0)) (PreH26 : (critical_region_interval critical sg invocation checkpoint current )) (PreH27 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH28 : (mem_create_profile sg )) (PreH29 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH30 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH31 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH32 : (mem_create_safe critical sg invocation base count size output before X )) (PreH33 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mem_create_cursor_resources sg current private (i + 1 ) caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private (i + 1 ) caller_frame X )
.

Definition OSMemCreate_return_wit_1 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome ((memory_control_addr (sg) ((memPrivateSlot (private))))) (0)) (mem_create_publish_state (current) (private)) )) (PreH3 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) (PreH4 : (i = (count - 1 ))) (PreH5 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH10 : (i >= loops)) (PreH11 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH12 : (mode = MemCreateArena)) (PreH13 : ((memPrivateBase (private)) = base)) (PreH14 : ((memPrivateBlockCount (private)) = count)) (PreH15 : ((memPrivateBlockSize (private)) = size)) (PreH16 : (memory_private_initialization_valid private )) (PreH17 : (loops = (count - 1 ))) (PreH18 : (0 <= i)) (PreH19 : (i <= (count - 1 ))) (PreH20 : (pblk = (base + (i * size ) ))) (PreH21 : (plink = (base + (i * size ) ))) (PreH22 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH23 : (mode = MemCreateArena)) (PreH24 : ((memPrivateBase (private)) = base)) (PreH25 : ((memPrivateBlockCount (private)) = count)) (PreH26 : ((memPrivateBlockSize (private)) = size)) (PreH27 : (memory_private_initialization_valid private )) (PreH28 : (pmem <> 0)) (PreH29 : (critical_region_interval critical sg invocation checkpoint current )) (PreH30 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH31 : (mem_create_profile sg )) (PreH32 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH33 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH34 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH35 : (mem_create_safe critical sg invocation base count size output before X )) (PreH36 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((output) # UChar  |-> 0)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) ((memory_control_addr (sg) ((memPrivateSlot (private))))) ((mem_create_publish_state (current) (private))) (caller_frame)) output )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before (memory_control_addr (sg) ((memPrivateSlot (private)))) caller_frame X )
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome ((memory_control_addr (sg) ((memPrivateSlot (private))))) (0)) (mem_create_publish_state (current) (private)) )) (PreH2 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) (PreH3 : (i = (count - 1 ))) (PreH4 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH9 : (i >= loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((output) # UChar  |-> 0)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) ((memory_control_addr (sg) ((memPrivateSlot (private))))) ((mem_create_publish_state (current) (private))) (caller_frame)) output )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before (memory_control_addr (sg) ((memPrivateSlot (private)))) caller_frame X )
).

Definition OSMemCreate_return_wit_1_split_goal_spatial := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome ((memory_control_addr (sg) ((memPrivateSlot (private))))) (0)) (mem_create_publish_state (current) (private)) )) (PreH2 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) (PreH3 : (i = (count - 1 ))) (PreH4 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH9 : (i >= loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((output) # UChar  |-> 0)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) ((memory_control_addr (sg) ((memPrivateSlot (private))))) ((mem_create_publish_state (current) (private))) (caller_frame)) output )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before (memory_control_addr (sg) ((memPrivateSlot (private)))) caller_frame X )
.

Definition OSMemCreate_return_wit_2 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (0 = 0)) (PreH2 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (0) (90)) current )) (PreH3 : (pmem = 0)) (PreH4 : (critical_region_interval critical sg invocation checkpoint current )) (PreH5 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH8 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH9 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH10 : (mem_create_safe critical sg invocation base count size output before X )) (PreH11 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 90)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (current) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (0) (90)) current )) (PreH2 : (pmem = 0)) (PreH3 : (critical_region_interval critical sg invocation checkpoint current )) (PreH4 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH7 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH8 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH9 : (mem_create_safe critical sg invocation base count size output before X )) (PreH10 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 90)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (current) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
).

Definition OSMemCreate_return_wit_2_split_goal_spatial := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (0) (90)) current )) (PreH2 : (pmem = 0)) (PreH3 : (critical_region_interval critical sg invocation checkpoint current )) (PreH4 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH7 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH8 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH9 : (mem_create_safe critical sg invocation base count size output before X )) (PreH10 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 90)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (current) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
.

Definition OSMemCreate_return_wit_3 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre < sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 92)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre < sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 92)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
).

Definition OSMemCreate_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre < sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 92)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
.

Definition OSMemCreate_return_wit_4 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (nblks_pre < 2)) (PreH2 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH3 : (addr_pre <> 0)) (PreH4 : (mem_create_arguments_in_range base count size )) (PreH5 : (blksize_pre <= UINT_MAX)) (PreH6 : (nblks_pre <= UINT_MAX)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (blksize_pre >= 0)) (PreH9 : (nblks_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (addr_pre = base)) (PreH12 : (nblks_pre = count)) (PreH13 : (blksize_pre = size)) (PreH14 : (perr_pre = output)) (PreH15 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH16 : (mem_create_profile sg )) (PreH17 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 91)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (nblks_pre < 2)) (PreH2 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH3 : (addr_pre <> 0)) (PreH4 : (mem_create_arguments_in_range base count size )) (PreH5 : (blksize_pre <= UINT_MAX)) (PreH6 : (nblks_pre <= UINT_MAX)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (blksize_pre >= 0)) (PreH9 : (nblks_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (addr_pre = base)) (PreH12 : (nblks_pre = count)) (PreH13 : (blksize_pre = size)) (PreH14 : (perr_pre = output)) (PreH15 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH16 : (mem_create_profile sg )) (PreH17 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 91)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
).

Definition OSMemCreate_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (nblks_pre < 2)) (PreH2 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH3 : (addr_pre <> 0)) (PreH4 : (mem_create_arguments_in_range base count size )) (PreH5 : (blksize_pre <= UINT_MAX)) (PreH6 : (nblks_pre <= UINT_MAX)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (blksize_pre >= 0)) (PreH9 : (nblks_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (addr_pre = base)) (PreH12 : (nblks_pre = count)) (PreH13 : (blksize_pre = size)) (PreH14 : (perr_pre = output)) (PreH15 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH16 : (mem_create_profile sg )) (PreH17 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 91)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
.

Definition OSMemCreate_return_wit_5 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0)) (PreH2 : (addr_pre <> 0)) (PreH3 : (mem_create_arguments_in_range base count size )) (PreH4 : (blksize_pre <= UINT_MAX)) (PreH5 : (nblks_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (blksize_pre >= 0)) (PreH8 : (nblks_pre >= 0)) (PreH9 : (0 >= 0)) (PreH10 : (addr_pre = base)) (PreH11 : (nblks_pre = count)) (PreH12 : (blksize_pre = size)) (PreH13 : (perr_pre = output)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH17 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH18 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH19 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0)) (PreH2 : (addr_pre <> 0)) (PreH3 : (mem_create_arguments_in_range base count size )) (PreH4 : (blksize_pre <= UINT_MAX)) (PreH5 : (nblks_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (blksize_pre >= 0)) (PreH8 : (nblks_pre >= 0)) (PreH9 : (0 >= 0)) (PreH10 : (addr_pre = base)) (PreH11 : (nblks_pre = count)) (PreH12 : (blksize_pre = size)) (PreH13 : (perr_pre = output)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH17 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH18 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH19 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
).

Definition OSMemCreate_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0)) (PreH2 : (addr_pre <> 0)) (PreH3 : (mem_create_arguments_in_range base count size )) (PreH4 : (blksize_pre <= UINT_MAX)) (PreH5 : (nblks_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (blksize_pre >= 0)) (PreH8 : (nblks_pre >= 0)) (PreH9 : (0 >= 0)) (PreH10 : (addr_pre = base)) (PreH11 : (nblks_pre = count)) (PreH12 : (blksize_pre = size)) (PreH13 : (perr_pre = output)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH17 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH18 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH19 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
.

Definition OSMemCreate_return_wit_6 := 
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = 0)) (PreH2 : (mem_create_arguments_in_range base count size )) (PreH3 : (blksize_pre <= UINT_MAX)) (PreH4 : (nblks_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (blksize_pre >= 0)) (PreH7 : (nblks_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (addr_pre = base)) (PreH10 : (nblks_pre = count)) (PreH11 : (blksize_pre = size)) (PreH12 : (perr_pre = output)) (PreH13 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH14 : (mem_create_profile sg )) (PreH15 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH16 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH17 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH18 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
) \/
(
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = 0)) (PreH2 : (mem_create_arguments_in_range base count size )) (PreH3 : (blksize_pre <= UINT_MAX)) (PreH4 : (nblks_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (blksize_pre >= 0)) (PreH7 : (nblks_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (addr_pre = base)) (PreH10 : (nblks_pre = count)) (PreH11 : (blksize_pre = size)) (PreH12 : (perr_pre = output)) (PreH13 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH14 : (mem_create_profile sg )) (PreH15 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH16 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH17 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH18 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
).

Definition OSMemCreate_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = 0)) (PreH2 : (mem_create_arguments_in_range base count size )) (PreH3 : (blksize_pre <= UINT_MAX)) (PreH4 : (nblks_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (blksize_pre >= 0)) (PreH7 : (nblks_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (addr_pre = base)) (PreH10 : (nblks_pre = count)) (PreH11 : (blksize_pre = size)) (PreH12 : (perr_pre = output)) (PreH13 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH14 : (mem_create_profile sg )) (PreH15 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH16 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH17 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH18 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |-> 98)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
|--
  (mem_create_api_post platform critical sg invocation origin mask mode base count size output before 0 caller_frame X )
.

Definition OSMemCreate_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = 0)) (PreH2 : (mem_create_arguments_in_range base count size )) (PreH3 : (blksize_pre <= UINT_MAX)) (PreH4 : (nblks_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (blksize_pre >= 0)) (PreH7 : (nblks_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (addr_pre = base)) (PreH10 : (nblks_pre = count)) (PreH11 : (blksize_pre = size)) (PreH12 : (perr_pre = output)) (PreH13 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH14 : (mem_create_profile sg )) (PreH15 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH16 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH17 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH18 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (addr_pre = 0)) (PreH2 : (mem_create_arguments_in_range base count size )) (PreH3 : (blksize_pre <= UINT_MAX)) (PreH4 : (nblks_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (blksize_pre >= 0)) (PreH7 : (nblks_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (addr_pre = base)) (PreH10 : (nblks_pre = count)) (PreH11 : (blksize_pre = size)) (PreH12 : (perr_pre = output)) (PreH13 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH14 : (mem_create_profile sg )) (PreH15 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH16 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH17 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH18 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (addr_pre = 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_1 := OSMemCreate_partial_solve_wit_1_pure -> OSMemCreate_partial_solve_wit_1_aux.

Definition OSMemCreate_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0)) (PreH2 : (addr_pre <> 0)) (PreH3 : (mem_create_arguments_in_range base count size )) (PreH4 : (blksize_pre <= UINT_MAX)) (PreH5 : (nblks_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (blksize_pre >= 0)) (PreH8 : (nblks_pre >= 0)) (PreH9 : (0 >= 0)) (PreH10 : (addr_pre = base)) (PreH11 : (nblks_pre = count)) (PreH12 : (blksize_pre = size)) (PreH13 : (perr_pre = output)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH17 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH18 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH19 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0)) (PreH2 : (addr_pre <> 0)) (PreH3 : (mem_create_arguments_in_range base count size )) (PreH4 : (blksize_pre <= UINT_MAX)) (PreH5 : (nblks_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (blksize_pre >= 0)) (PreH8 : (nblks_pre >= 0)) (PreH9 : (0 >= 0)) (PreH10 : (addr_pre = base)) (PreH11 : (nblks_pre = count)) (PreH12 : (blksize_pre = size)) (PreH13 : (perr_pre = output)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH17 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH18 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH19 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) <> 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_2 := OSMemCreate_partial_solve_wit_2_pure -> OSMemCreate_partial_solve_wit_2_aux.

Definition OSMemCreate_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (nblks_pre < 2)) (PreH2 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH3 : (addr_pre <> 0)) (PreH4 : (mem_create_arguments_in_range base count size )) (PreH5 : (blksize_pre <= UINT_MAX)) (PreH6 : (nblks_pre <= UINT_MAX)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (blksize_pre >= 0)) (PreH9 : (nblks_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (addr_pre = base)) (PreH12 : (nblks_pre = count)) (PreH13 : (blksize_pre = size)) (PreH14 : (perr_pre = output)) (PreH15 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH16 : (mem_create_profile sg )) (PreH17 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (nblks_pre < 2)) (PreH2 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH3 : (addr_pre <> 0)) (PreH4 : (mem_create_arguments_in_range base count size )) (PreH5 : (blksize_pre <= UINT_MAX)) (PreH6 : (nblks_pre <= UINT_MAX)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (blksize_pre >= 0)) (PreH9 : (nblks_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (addr_pre = base)) (PreH12 : (nblks_pre = count)) (PreH13 : (blksize_pre = size)) (PreH14 : (perr_pre = output)) (PreH15 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH16 : (mem_create_profile sg )) (PreH17 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (nblks_pre < 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_3 := OSMemCreate_partial_solve_wit_3_pure -> OSMemCreate_partial_solve_wit_3_aux.

Definition OSMemCreate_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre < sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (blksize_pre < sizeof(PTR))) (PreH2 : (nblks_pre >= 2)) (PreH3 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH4 : (addr_pre <> 0)) (PreH5 : (mem_create_arguments_in_range base count size )) (PreH6 : (blksize_pre <= UINT_MAX)) (PreH7 : (nblks_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (blksize_pre >= 0)) (PreH10 : (nblks_pre >= 0)) (PreH11 : (0 >= 0)) (PreH12 : (addr_pre = base)) (PreH13 : (nblks_pre = count)) (PreH14 : (blksize_pre = size)) (PreH15 : (perr_pre = output)) (PreH16 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH17 : (mem_create_profile sg )) (PreH18 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH19 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH20 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH21 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (blksize_pre < sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> output)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_4 := OSMemCreate_partial_solve_wit_4_pure -> OSMemCreate_partial_solve_wit_4_aux.

Definition OSMemCreate_partial_solve_wit_5 := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_arguments_valid base count size )) (PreH2 : (blksize_pre >= sizeof(PTR))) (PreH3 : (nblks_pre >= 2)) (PreH4 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH5 : (addr_pre <> 0)) (PreH6 : (mem_create_arguments_in_range base count size )) (PreH7 : (blksize_pre <= UINT_MAX)) (PreH8 : (nblks_pre <= UINT_MAX)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (blksize_pre >= 0)) (PreH11 : (nblks_pre >= 0)) (PreH12 : (0 >= 0)) (PreH13 : (addr_pre = base)) (PreH14 : (nblks_pre = count)) (PreH15 : (blksize_pre = size)) (PreH16 : (perr_pre = output)) (PreH17 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH18 : (mem_create_profile sg )) (PreH19 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH20 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH21 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH22 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (blksize_pre >= sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (mem_create_arguments_valid base count size )) (PreH5 : (blksize_pre >= sizeof(PTR))) (PreH6 : (nblks_pre >= 2)) (PreH7 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH8 : (addr_pre <> 0)) (PreH9 : (mem_create_arguments_in_range base count size )) (PreH10 : (blksize_pre <= UINT_MAX)) (PreH11 : (nblks_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (blksize_pre >= 0)) (PreH14 : (nblks_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (addr_pre = base)) (PreH17 : (nblks_pre = count)) (PreH18 : (blksize_pre = size)) (PreH19 : (perr_pre = output)) (PreH20 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH21 : (mem_create_profile sg )) (PreH22 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH23 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH24 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH25 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (mem_create_arguments_valid base count size )) (PreH5 : (blksize_pre >= sizeof(PTR))) (PreH6 : (nblks_pre >= 2)) (PreH7 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH8 : (addr_pre <> 0)) (PreH9 : (mem_create_arguments_in_range base count size )) (PreH10 : (blksize_pre <= UINT_MAX)) (PreH11 : (nblks_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (blksize_pre >= 0)) (PreH14 : (nblks_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (addr_pre = base)) (PreH17 : (nblks_pre = count)) (PreH18 : (blksize_pre = size)) (PreH19 : (perr_pre = output)) (PreH20 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH21 : (mem_create_profile sg )) (PreH22 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH23 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH24 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH25 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (blksize_pre >= sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemCreate_partial_solve_wit_6 := OSMemCreate_partial_solve_wit_6_pure -> OSMemCreate_partial_solve_wit_6_aux.

Definition OSMemCreate_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH2 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH3 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval >= 0)) (PreH6 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_arguments_valid base count size )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH11 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (mem_create_arguments_valid base count size )) (PreH17 : (blksize_pre >= sizeof(PTR))) (PreH18 : (nblks_pre >= 2)) (PreH19 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH20 : (addr_pre <> 0)) (PreH21 : (mem_create_arguments_in_range base count size )) (PreH22 : (blksize_pre <= UINT_MAX)) (PreH23 : (nblks_pre <= UINT_MAX)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (blksize_pre >= 0)) (PreH26 : (nblks_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (addr_pre = base)) (PreH29 : (nblks_pre = count)) (PreH30 : (blksize_pre = size)) (PreH31 : (perr_pre = output)) (PreH32 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH33 : (mem_create_profile sg )) (PreH34 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH35 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH36 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH37 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
|--
  “ ((mem_create_free_head (sg) (entry)) = (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (0 <= (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) < 4294967296) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ”
.

Definition OSMemCreate_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH2 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH3 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval >= 0)) (PreH6 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_arguments_valid base count size )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH11 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (mem_create_arguments_valid base count size )) (PreH17 : (blksize_pre >= sizeof(PTR))) (PreH18 : (nblks_pre >= 2)) (PreH19 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH20 : (addr_pre <> 0)) (PreH21 : (mem_create_arguments_in_range base count size )) (PreH22 : (blksize_pre <= UINT_MAX)) (PreH23 : (nblks_pre <= UINT_MAX)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (blksize_pre >= 0)) (PreH26 : (nblks_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (addr_pre = base)) (PreH29 : (nblks_pre = count)) (PreH30 : (blksize_pre = size)) (PreH31 : (perr_pre = output)) (PreH32 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH33 : (mem_create_profile sg )) (PreH34 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH35 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH36 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH37 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "addr" ) )) # Ptr  |-> addr_pre)
  **  ((( &( "nblks" ) )) # UInt  |-> nblks_pre)
  **  ((( &( "blksize" ) )) # UInt  |-> blksize_pre)
|--
  “ ((mem_create_free_head (sg) (entry)) = (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (0 <= (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) < 4294967296) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (0 <= (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) < 4294967296) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (blksize_pre >= sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  (mem_create_root_frame sg entry )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemCreate_partial_solve_wit_7 := OSMemCreate_partial_solve_wit_7_pure -> OSMemCreate_partial_solve_wit_7_aux.

Definition OSMemCreate_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (PreH1 : ((mem_create_free_head (sg) (entry)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mode = MemCreateArena)) (PreH6 : (mem_create_arguments_valid base count size )) (PreH7 : (critical_region_interval critical sg invocation before entry )) (PreH8 : (mem_create_reservation sg base count size entry private post )) (PreH9 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH10 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH11 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_arguments_valid base count size )) (PreH17 : (critical_region_interval critical sg invocation before entry )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (UCOS2_state_inv sg entry )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (UCOS2_state_inv sg entry )) (PreH23 : (interrupt_saved_value mask retval )) (PreH24 : (mem_create_arguments_valid base count size )) (PreH25 : (blksize_pre >= sizeof(PTR))) (PreH26 : (nblks_pre >= 2)) (PreH27 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH28 : (addr_pre <> 0)) (PreH29 : (mem_create_arguments_in_range base count size )) (PreH30 : (blksize_pre <= UINT_MAX)) (PreH31 : (nblks_pre <= UINT_MAX)) (PreH32 : (0 <= UINT_MAX)) (PreH33 : (blksize_pre >= 0)) (PreH34 : (nblks_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (addr_pre = base)) (PreH37 : (nblks_pre = count)) (PreH38 : (blksize_pre = size)) (PreH39 : (perr_pre = output)) (PreH40 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH41 : (mem_create_profile sg )) (PreH42 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH43 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH44 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH45 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((&(((mem_create_free_head (sg) (entry)))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
|--
  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_create_reservation sg base count size entry private post ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (blksize_pre: Z) (nblks_pre: Z) (addr_pre: Z) (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (PreH1 : ((mem_create_free_head (sg) (entry)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mode = MemCreateArena)) (PreH6 : (mem_create_arguments_valid base count size )) (PreH7 : (critical_region_interval critical sg invocation before entry )) (PreH8 : (mem_create_reservation sg base count size entry private post )) (PreH9 : ((mem_create_free_head (sg) (entry)) <> 0)) (PreH10 : (0 <= (mem_create_free_head (sg) (entry)))) (PreH11 : ((mem_create_free_head (sg) (entry)) < 4294967296)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH15 : (mem_create_profile sg )) (PreH16 : (mem_create_arguments_valid base count size )) (PreH17 : (critical_region_interval critical sg invocation before entry )) (PreH18 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH19 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) (PreH20 : (UCOS2_state_inv sg entry )) (PreH21 : (critical_region_interval critical sg invocation before entry )) (PreH22 : (UCOS2_state_inv sg entry )) (PreH23 : (interrupt_saved_value mask retval )) (PreH24 : (mem_create_arguments_valid base count size )) (PreH25 : (blksize_pre >= sizeof(PTR))) (PreH26 : (nblks_pre >= 2)) (PreH27 : ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0)) (PreH28 : (addr_pre <> 0)) (PreH29 : (mem_create_arguments_in_range base count size )) (PreH30 : (blksize_pre <= UINT_MAX)) (PreH31 : (nblks_pre <= UINT_MAX)) (PreH32 : (0 <= UINT_MAX)) (PreH33 : (blksize_pre >= 0)) (PreH34 : (nblks_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (addr_pre = base)) (PreH37 : (nblks_pre = count)) (PreH38 : (blksize_pre = size)) (PreH39 : (perr_pre = output)) (PreH40 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH41 : (mem_create_profile sg )) (PreH42 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH43 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH44 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) (PreH45 : (mem_create_safe critical sg invocation base count size output before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  ((&(((mem_create_free_head (sg) (entry)))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_create_reservation sg base count size entry private post ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_reservation sg base count size entry private post ) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (0 <= (mem_create_free_head (sg) (entry))) ” 
  &&  “ ((mem_create_free_head (sg) (entry)) < 4294967296) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (blksize_pre >= sizeof(PTR)) ” 
  &&  “ (nblks_pre >= 2) ” 
  &&  “ ((Z.land addr_pre (sizeof(PTR) - 1 )) = 0) ” 
  &&  “ (addr_pre <> 0) ” 
  &&  “ (mem_create_arguments_in_range base count size ) ” 
  &&  “ (blksize_pre <= UINT_MAX) ” 
  &&  “ (nblks_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (blksize_pre >= 0) ” 
  &&  “ (nblks_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (addr_pre = base) ” 
  &&  “ (nblks_pre = count) ” 
  &&  “ (blksize_pre = size) ” 
  &&  “ (perr_pre = output) ” 
  &&  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> (memory_control_addr (sg) ((memPrivateSlot (private)))))
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemCreate_partial_solve_wit_8 := OSMemCreate_partial_solve_wit_8_pure -> OSMemCreate_partial_solve_wit_8_aux.

Definition OSMemCreate_partial_solve_wit_9 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (PreH1 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH4 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_safe critical sg invocation base count size output before X )) (PreH7 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry checkpoint )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry checkpoint )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_10_pure := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (pmem = 0)) (PreH2 : (critical_region_interval critical sg invocation checkpoint current )) (PreH3 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH6 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
|--
  “ (0 = 0) ” 
  &&  “ (0 = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_10_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (pmem = 0)) (PreH2 : (critical_region_interval critical sg invocation checkpoint current )) (PreH3 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH6 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem)
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (0 = 0) ” 
  &&  “ (0 = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (pmem = 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> 0)
  **  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_10 := OSMemCreate_partial_solve_wit_10_pure -> OSMemCreate_partial_solve_wit_10_aux.

Definition OSMemCreate_partial_solve_wit_11_pure := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (cpu_sr: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (pmem <> 0)) (PreH2 : (critical_region_interval critical sg invocation checkpoint current )) (PreH3 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH6 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
  **  ((( &( "pblk" ) )) # Ptr  |->_)
  **  ((( &( "plink" ) )) # Ptr  |->_)
  **  ((( &( "loops" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
|--
  “ ((mem_create_selected_pointer (sg) (selected)) <> 0) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ”
.

Definition OSMemCreate_partial_solve_wit_11_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (pmem <> 0)) (PreH2 : (critical_region_interval critical sg invocation checkpoint current )) (PreH3 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH6 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem)
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ ((mem_create_selected_pointer (sg) (selected)) <> 0) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> (mem_create_selected_pointer (sg) (selected)))
  **  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_partial_solve_wit_11 := OSMemCreate_partial_solve_wit_11_pure -> OSMemCreate_partial_solve_wit_11_aux.

Definition OSMemCreate_partial_solve_wit_12_pure := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i < loops)) (PreH2 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mode = MemCreateArena)) (PreH4 : ((memPrivateBase (private)) = base)) (PreH5 : ((memPrivateBlockCount (private)) = count)) (PreH6 : ((memPrivateBlockSize (private)) = size)) (PreH7 : (memory_private_initialization_valid private )) (PreH8 : (loops = (count - 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (count - 1 ))) (PreH11 : (pblk = (base + (i * size ) ))) (PreH12 : (plink = (base + (i * size ) ))) (PreH13 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH14 : (mode = MemCreateArena)) (PreH15 : ((memPrivateBase (private)) = base)) (PreH16 : ((memPrivateBlockCount (private)) = count)) (PreH17 : ((memPrivateBlockSize (private)) = size)) (PreH18 : (memory_private_initialization_valid private )) (PreH19 : (pmem <> 0)) (PreH20 : (critical_region_interval critical sg invocation checkpoint current )) (PreH21 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH22 : (mem_create_profile sg )) (PreH23 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH24 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH25 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH26 : (mem_create_safe critical sg invocation base count size output before X )) (PreH27 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pblk" ) )) # Ptr  |-> (pblk + (size * sizeof(UCHAR))))
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ” 
  &&  “ ((base + (i * size ) ) = (base + (i * size ) )) ” 
  &&  “ ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ”
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i <= UINT_MAX)) (PreH2 : (loops <= UINT_MAX)) (PreH3 : (size <= UINT_MAX)) (PreH4 : (count <= UINT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (loops >= 0)) (PreH7 : (size >= 0)) (PreH8 : (count >= 0)) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pblk" ) )) # Ptr  |-> (pblk + (size * sizeof(UCHAR))))
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ”
).

Definition OSMemCreate_partial_solve_wit_12_pure_split_goal_1 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i <= UINT_MAX)) (PreH2 : (loops <= UINT_MAX)) (PreH3 : (size <= UINT_MAX)) (PreH4 : (count <= UINT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (loops >= 0)) (PreH7 : (size >= 0)) (PreH8 : (count >= 0)) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pblk" ) )) # Ptr  |-> (pblk + (size * sizeof(UCHAR))))
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ”
.

Definition OSMemCreate_partial_solve_wit_12_pure_split_goal_2 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i <= UINT_MAX)) (PreH2 : (loops <= UINT_MAX)) (PreH3 : (size <= UINT_MAX)) (PreH4 : (count <= UINT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (loops >= 0)) (PreH7 : (size >= 0)) (PreH8 : (count >= 0)) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pblk" ) )) # Ptr  |-> (pblk + (size * sizeof(UCHAR))))
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ”
.

Definition OSMemCreate_partial_solve_wit_12_pure_split_goal_3 := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i <= UINT_MAX)) (PreH2 : (loops <= UINT_MAX)) (PreH3 : (size <= UINT_MAX)) (PreH4 : (count <= UINT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (loops >= 0)) (PreH7 : (size >= 0)) (PreH8 : (count >= 0)) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pblk" ) )) # Ptr  |-> (pblk + (size * sizeof(UCHAR))))
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ”
.

Definition OSMemCreate_partial_solve_wit_12_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i < loops)) (PreH2 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mode = MemCreateArena)) (PreH4 : ((memPrivateBase (private)) = base)) (PreH5 : ((memPrivateBlockCount (private)) = count)) (PreH6 : ((memPrivateBlockSize (private)) = size)) (PreH7 : (memory_private_initialization_valid private )) (PreH8 : (loops = (count - 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (count - 1 ))) (PreH11 : (pblk = (base + (i * size ) ))) (PreH12 : (plink = (base + (i * size ) ))) (PreH13 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH14 : (mode = MemCreateArena)) (PreH15 : ((memPrivateBase (private)) = base)) (PreH16 : ((memPrivateBlockCount (private)) = count)) (PreH17 : ((memPrivateBlockSize (private)) = size)) (PreH18 : (memory_private_initialization_valid private )) (PreH19 : (pmem <> 0)) (PreH20 : (critical_region_interval critical sg invocation checkpoint current )) (PreH21 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH22 : (mem_create_profile sg )) (PreH23 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH24 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH25 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH26 : (mem_create_safe critical sg invocation base count size output before X )) (PreH27 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "pblk" ) )) # Ptr  |-> (pblk + (size * sizeof(UCHAR))))
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
|--
  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ” 
  &&  “ ((base + (i * size ) ) = (base + (i * size ) )) ” 
  &&  “ ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (((base + (i * size ) ) + (size * sizeof(UCHAR))) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (i < loops) ” 
  &&  “ (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ (pblk = (base + (i * size ) )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "plink" ) )) # Ptr  |-> (base + (i * size ) ))
  **  ((( &( "pblk" ) )) # Ptr  |-> (base + ((i + 1 ) * size ) ))
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
.

Definition OSMemCreate_partial_solve_wit_12 := OSMemCreate_partial_solve_wit_12_pure -> OSMemCreate_partial_solve_wit_12_aux.

Definition OSMemCreate_partial_solve_wit_13_pure := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (count - 1 ))) (PreH3 : ((base + (i * size ) ) = (base + (i * size ) ))) (PreH4 : ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) ))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output )) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "plink" ) )) # Ptr  |-> (base + (i * size ) ))
  **  ((( &( "pblk" ) )) # Ptr  |-> (base + ((i + 1 ) * size ) ))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((base + (i * size ) )) # Ptr  |-> (base + ((i + 1 ) * size ) ))
  **  (mem_create_loop_resources sg current private i caller_frame )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((base + (i * size ) ) = (base + (i * size ) )) ” 
  &&  “ ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ”
.

Definition OSMemCreate_partial_solve_wit_13_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (count - 1 ))) (PreH3 : ((base + (i * size ) ) = (base + (i * size ) ))) (PreH4 : ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) ))) (PreH5 : (mem_create_profile sg )) (PreH6 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH7 : (mem_create_safe critical sg invocation base count size output before X )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output )) (PreH9 : (i < loops)) (PreH10 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH11 : (mode = MemCreateArena)) (PreH12 : ((memPrivateBase (private)) = base)) (PreH13 : ((memPrivateBlockCount (private)) = count)) (PreH14 : ((memPrivateBlockSize (private)) = size)) (PreH15 : (memory_private_initialization_valid private )) (PreH16 : (loops = (count - 1 ))) (PreH17 : (0 <= i)) (PreH18 : (i <= (count - 1 ))) (PreH19 : (pblk = (base + (i * size ) ))) (PreH20 : (plink = (base + (i * size ) ))) (PreH21 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH22 : (mode = MemCreateArena)) (PreH23 : ((memPrivateBase (private)) = base)) (PreH24 : ((memPrivateBlockCount (private)) = count)) (PreH25 : ((memPrivateBlockSize (private)) = size)) (PreH26 : (memory_private_initialization_valid private )) (PreH27 : (pmem <> 0)) (PreH28 : (critical_region_interval critical sg invocation checkpoint current )) (PreH29 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH30 : (mem_create_profile sg )) (PreH31 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH32 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH33 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH34 : (mem_create_safe critical sg invocation base count size output before X )) (PreH35 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (((base + (i * size ) )) # Ptr  |-> (base + ((i + 1 ) * size ) ))
  **  (mem_create_loop_resources sg current private i caller_frame )
|--
  “ ((base + (i * size ) ) = (base + (i * size ) )) ” 
  &&  “ ((base + ((i + 1 ) * size ) ) = (base + ((i + 1 ) * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output ) ” 
  &&  “ (i < loops) ” 
  &&  “ (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ (pblk = (base + (i * size ) )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (((base + (i * size ) )) # Ptr  |-> (base + ((i + 1 ) * size ) ))
  **  (mem_create_loop_resources sg current private i caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMemCreate_partial_solve_wit_13 := OSMemCreate_partial_solve_wit_13_pure -> OSMemCreate_partial_solve_wit_13_aux.

Definition OSMemCreate_partial_solve_wit_14_pure := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i >= loops)) (PreH2 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mode = MemCreateArena)) (PreH4 : ((memPrivateBase (private)) = base)) (PreH5 : ((memPrivateBlockCount (private)) = count)) (PreH6 : ((memPrivateBlockSize (private)) = size)) (PreH7 : (memory_private_initialization_valid private )) (PreH8 : (loops = (count - 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (count - 1 ))) (PreH11 : (pblk = (base + (i * size ) ))) (PreH12 : (plink = (base + (i * size ) ))) (PreH13 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH14 : (mode = MemCreateArena)) (PreH15 : ((memPrivateBase (private)) = base)) (PreH16 : ((memPrivateBlockCount (private)) = count)) (PreH17 : ((memPrivateBlockSize (private)) = size)) (PreH18 : (memory_private_initialization_valid private )) (PreH19 : (pmem <> 0)) (PreH20 : (critical_region_interval critical sg invocation checkpoint current )) (PreH21 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH22 : (mem_create_profile sg )) (PreH23 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH24 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH25 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH26 : (mem_create_safe critical sg invocation base count size output before X )) (PreH27 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk)
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((count - 1 ) = (count - 1 )) ” 
  &&  “ (i >= (count - 1 )) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ ((base + (i * size ) ) = (base + (i * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ”
.

Definition OSMemCreate_partial_solve_wit_14_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i >= loops)) (PreH2 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mode = MemCreateArena)) (PreH4 : ((memPrivateBase (private)) = base)) (PreH5 : ((memPrivateBlockCount (private)) = count)) (PreH6 : ((memPrivateBlockSize (private)) = size)) (PreH7 : (memory_private_initialization_valid private )) (PreH8 : (loops = (count - 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (count - 1 ))) (PreH11 : (pblk = (base + (i * size ) ))) (PreH12 : (plink = (base + (i * size ) ))) (PreH13 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH14 : (mode = MemCreateArena)) (PreH15 : ((memPrivateBase (private)) = base)) (PreH16 : ((memPrivateBlockCount (private)) = count)) (PreH17 : ((memPrivateBlockSize (private)) = size)) (PreH18 : (memory_private_initialization_valid private )) (PreH19 : (pmem <> 0)) (PreH20 : (critical_region_interval critical sg invocation checkpoint current )) (PreH21 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH22 : (mem_create_profile sg )) (PreH23 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH24 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH25 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH26 : (mem_create_safe critical sg invocation base count size output before X )) (PreH27 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "loops" ) )) # UInt  |-> loops)
  **  ((( &( "plink" ) )) # Ptr  |-> plink)
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
|--
  “ ((count - 1 ) = (count - 1 )) ” 
  &&  “ (i >= (count - 1 )) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ ((base + (i * size ) ) = (base + (i * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (i >= loops) ” 
  &&  “ (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ (pblk = (base + (i * size ) )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "loops" ) )) # UInt  |-> (count - 1 ))
  **  ((( &( "plink" ) )) # Ptr  |-> (base + (i * size ) ))
  **  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
.

Definition OSMemCreate_partial_solve_wit_14 := OSMemCreate_partial_solve_wit_14_pure -> OSMemCreate_partial_solve_wit_14_aux.

Definition OSMemCreate_partial_solve_wit_15_pure := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i = (count - 1 ))) (PreH2 : ((count - 1 ) = (count - 1 ))) (PreH3 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH6 : (mem_create_safe critical sg invocation base count size output before X )) (PreH7 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH8 : (i >= loops)) (PreH9 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH10 : (mode = MemCreateArena)) (PreH11 : ((memPrivateBase (private)) = base)) (PreH12 : ((memPrivateBlockCount (private)) = count)) (PreH13 : ((memPrivateBlockSize (private)) = size)) (PreH14 : (memory_private_initialization_valid private )) (PreH15 : (loops = (count - 1 ))) (PreH16 : (0 <= i)) (PreH17 : (i <= (count - 1 ))) (PreH18 : (pblk = (base + (i * size ) ))) (PreH19 : (plink = (base + (i * size ) ))) (PreH20 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH21 : (mode = MemCreateArena)) (PreH22 : ((memPrivateBase (private)) = base)) (PreH23 : ((memPrivateBlockCount (private)) = count)) (PreH24 : ((memPrivateBlockSize (private)) = size)) (PreH25 : (memory_private_initialization_valid private )) (PreH26 : (pmem <> 0)) (PreH27 : (critical_region_interval critical sg invocation checkpoint current )) (PreH28 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH29 : (mem_create_profile sg )) (PreH30 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH31 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH32 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH33 : (mem_create_safe critical sg invocation base count size output before X )) (PreH34 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "loops" ) )) # UInt  |-> (count - 1 ))
  **  ((( &( "plink" ) )) # Ptr  |-> (base + (i * size ) ))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((base + (i * size ) )) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ ((base + ((count - 1 ) * size ) ) = (base + ((count - 1 ) * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_15_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : (i = (count - 1 ))) (PreH2 : ((count - 1 ) = (count - 1 ))) (PreH3 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH4 : (mem_create_profile sg )) (PreH5 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH6 : (mem_create_safe critical sg invocation base count size output before X )) (PreH7 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH8 : (i >= loops)) (PreH9 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH10 : (mode = MemCreateArena)) (PreH11 : ((memPrivateBase (private)) = base)) (PreH12 : ((memPrivateBlockCount (private)) = count)) (PreH13 : ((memPrivateBlockSize (private)) = size)) (PreH14 : (memory_private_initialization_valid private )) (PreH15 : (loops = (count - 1 ))) (PreH16 : (0 <= i)) (PreH17 : (i <= (count - 1 ))) (PreH18 : (pblk = (base + (i * size ) ))) (PreH19 : (plink = (base + (i * size ) ))) (PreH20 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH21 : (mode = MemCreateArena)) (PreH22 : ((memPrivateBase (private)) = base)) (PreH23 : ((memPrivateBlockCount (private)) = count)) (PreH24 : ((memPrivateBlockSize (private)) = size)) (PreH25 : (memory_private_initialization_valid private )) (PreH26 : (pmem <> 0)) (PreH27 : (critical_region_interval critical sg invocation checkpoint current )) (PreH28 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH29 : (mem_create_profile sg )) (PreH30 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH31 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH32 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH33 : (mem_create_safe critical sg invocation base count size output before X )) (PreH34 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "plink" ) )) # Ptr  |-> (base + (i * size ) ))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((base + (i * size ) )) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_2)
|--
  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ ((base + ((count - 1 ) * size ) ) = (base + ((count - 1 ) * size ) )) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output ) ” 
  &&  “ (i = (count - 1 )) ” 
  &&  “ ((base + (i * size ) ) = (base + ((count - 1 ) * size ) )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output ) ” 
  &&  “ (i >= loops) ” 
  &&  “ (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ (pblk = (base + (i * size ) )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> (memory_control_addr (sg) ((memPrivateSlot (private)))))
  **  ((( &( "plink" ) )) # Ptr  |-> (base + ((count - 1 ) * size ) ))
  **  (((base + ((count - 1 ) * size ) )) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMemCreate_partial_solve_wit_15 := OSMemCreate_partial_solve_wit_15_pure -> OSMemCreate_partial_solve_wit_15_aux.

Definition OSMemCreate_partial_solve_wit_16_pure := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : ((base + ((count - 1 ) * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH3 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) (PreH4 : (i = (count - 1 ))) (PreH5 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH10 : (i >= loops)) (PreH11 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH12 : (mode = MemCreateArena)) (PreH13 : ((memPrivateBase (private)) = base)) (PreH14 : ((memPrivateBlockCount (private)) = count)) (PreH15 : ((memPrivateBlockSize (private)) = size)) (PreH16 : (memory_private_initialization_valid private )) (PreH17 : (loops = (count - 1 ))) (PreH18 : (0 <= i)) (PreH19 : (i <= (count - 1 ))) (PreH20 : (pblk = (base + (i * size ) ))) (PreH21 : (plink = (base + (i * size ) ))) (PreH22 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH23 : (mode = MemCreateArena)) (PreH24 : ((memPrivateBase (private)) = base)) (PreH25 : ((memPrivateBlockCount (private)) = count)) (PreH26 : ((memPrivateBlockSize (private)) = size)) (PreH27 : (memory_private_initialization_valid private )) (PreH28 : (pmem <> 0)) (PreH29 : (critical_region_interval critical sg invocation checkpoint current )) (PreH30 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH31 : (mem_create_profile sg )) (PreH32 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH33 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH34 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH35 : (mem_create_safe critical sg invocation base count size output before X )) (PreH36 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "pmem" ) )) # Ptr  |-> (memory_control_addr (sg) ((memPrivateSlot (private)))))
  **  ((( &( "plink" ) )) # Ptr  |-> (base + ((count - 1 ) * size ) ))
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> base)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> base)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> count)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> count)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> size)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "loops" ) )) # UInt  |-> (count - 1 ))
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "addr" ) )) # Ptr  |-> base)
  **  ((( &( "nblks" ) )) # UInt  |-> count)
  **  ((( &( "blksize" ) )) # UInt  |-> size)
  **  ((( &( "perr" ) )) # Ptr  |-> output)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output ) ”
.

Definition OSMemCreate_partial_solve_wit_16_aux := 
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (pmem: Z) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (pblk: Z) (i: Z) (loops: Z) (pmem_2: Z) (PreH1 : ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : ((base + ((count - 1 ) * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH3 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) (PreH4 : (i = (count - 1 ))) (PreH5 : ((base + (i * size ) ) = (base + ((count - 1 ) * size ) ))) (PreH6 : (mem_create_profile sg )) (PreH7 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH8 : (mem_create_safe critical sg invocation base count size output before X )) (PreH9 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) (PreH10 : (i >= loops)) (PreH11 : (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH12 : (mode = MemCreateArena)) (PreH13 : ((memPrivateBase (private)) = base)) (PreH14 : ((memPrivateBlockCount (private)) = count)) (PreH15 : ((memPrivateBlockSize (private)) = size)) (PreH16 : (memory_private_initialization_valid private )) (PreH17 : (loops = (count - 1 ))) (PreH18 : (0 <= i)) (PreH19 : (i <= (count - 1 ))) (PreH20 : (pblk = (base + (i * size ) ))) (PreH21 : (plink = (base + (i * size ) ))) (PreH22 : ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH23 : (mode = MemCreateArena)) (PreH24 : ((memPrivateBase (private)) = base)) (PreH25 : ((memPrivateBlockCount (private)) = count)) (PreH26 : ((memPrivateBlockSize (private)) = size)) (PreH27 : (memory_private_initialization_valid private )) (PreH28 : (pmem <> 0)) (PreH29 : (critical_region_interval critical sg invocation checkpoint current )) (PreH30 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH31 : (mem_create_profile sg )) (PreH32 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH33 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH34 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH35 : (mem_create_safe critical sg invocation base count size output before X )) (PreH36 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> base)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> base)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> count)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> count)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> size)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((memory_control_addr (sg) ((memPrivateSlot (private)))) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output ) ” 
  &&  “ (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output ) ” 
  &&  “ (i = (count - 1 )) ” 
  &&  “ ((base + (i * size ) ) = (base + ((count - 1 ) * size ) )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output ) ” 
  &&  “ (i >= loops) ” 
  &&  “ (pmem_2 = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (count - 1 )) ” 
  &&  “ (pblk = (base + (i * size ) )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ ((mem_create_selected_pointer (sg) (selected)) = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint current ) ” 
  &&  “ (pmem = (mem_create_selected_pointer (sg) (selected))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint ) ” 
  &&  “ (mem_create_call_domain critical sg invocation mode base count size before ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> base)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> base)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> count)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> count)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> size)
  **  ((&(((memory_control_addr (sg) ((memPrivateSlot (private)))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMemCreate_partial_solve_wit_16 := OSMemCreate_partial_solve_wit_16_pure -> OSMemCreate_partial_solve_wit_16_aux.

Definition OSMemCreate_which_implies_wit_1 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |->_)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (x: Z) ,
  ((output) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
).

Definition OSMemCreate_which_implies_wit_2 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |->_)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (x: Z) ,
  ((output) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
).

Definition OSMemCreate_which_implies_wit_3 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |->_)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (x: Z) ,
  ((output) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
).

Definition OSMemCreate_which_implies_wit_4 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |->_)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (x: Z) ,
  ((output) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (before) (caller_frame)) output )
).

Definition OSMemCreate_which_implies_wit_5 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_arguments_valid base count size )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg))) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_output_rely critical sg invocation mode base count size output caller_frame ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_arguments_valid base count size )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
).

Definition OSMemCreate_which_implies_wit_5_split_goal_1 := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_arguments_valid base count size )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSMemCreate_which_implies_wit_5_split_goal_2 := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_arguments_valid base count size )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_which_implies_wit_5_split_goal_spatial := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (mem_create_profile sg )) (PreH3 : (mem_create_arguments_valid base count size )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (before) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (UCOS2_inv sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (mem_create_free_head (sg) (entry)))
  **  (mem_create_root_frame sg entry )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_which_implies_wit_6 := 
(
forall (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (PreH1 : (pmem = (mem_create_free_head (sg) (entry)))) (PreH2 : (pmem <> 0)) (PreH3 : (0 <= pmem)) (PreH4 : (pmem < 4294967296)) (PreH5 : (mem_create_profile sg )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (mem_create_arguments_valid base count size )) (PreH10 : (mem_create_arguments_in_range base count size )) ,
  (mem_create_root_frame sg entry )
|--
  EX (post: GlobMemoryState)  (private: MemoryPrivatePartition) ,
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_reservation sg base count size entry private post ) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
) \/
(
forall (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (PreH1 : (pmem = (mem_create_free_head (sg) (entry)))) (PreH2 : (pmem <> 0)) (PreH3 : (0 <= pmem)) (PreH4 : (pmem < 4294967296)) (PreH5 : (mem_create_profile sg )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (mem_create_arguments_valid base count size )) (PreH10 : (mem_create_arguments_in_range base count size )) ,
  (mem_create_root_frame sg entry )
|--
  EX (post: GlobMemoryState)  (private: MemoryPrivatePartition) ,
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (pmem <> 0) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ (mem_create_arguments_valid base count size ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (mem_create_reservation sg base count size entry private post ) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
).

Definition OSMemCreate_which_implies_wit_7 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (pmem: Z) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mem_create_reservation sg base count size entry private post )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mem_create_reservation sg base count size entry private post ) ” 
  &&  “ (UCOS2_state_inv sg (replace_MemoryS (post) (entry)) ) ” 
  &&  “ (mem_create_byte_access (mem_create_detached_resources (sg) ((replace_MemoryS (post) (entry))) ((mem_create_selection (private))) (mode) (base) (count) (size) (caller_frame)) output ) ”
  &&  (UCOS2_inv sg (replace_MemoryS (post) (entry)) )
  **  (memory_private_control_rep sg private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (pmem: Z) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mem_create_reservation sg base count size entry private post )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_detached_resources (sg) ((replace_MemoryS (post) (entry))) ((mem_create_selection (private))) (mode) (base) (count) (size) (caller_frame)) output ) ” 
  &&  “ (UCOS2_state_inv sg (replace_MemoryS (post) (entry)) ) ”
  &&  (UCOS2_inv sg (replace_MemoryS (post) (entry)) )
  **  (memory_private_control_rep sg private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
).

Definition OSMemCreate_which_implies_wit_7_split_goal_1 := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (pmem: Z) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mem_create_reservation sg base count size entry private post )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (mem_create_byte_access (mem_create_detached_resources (sg) ((replace_MemoryS (post) (entry))) ((mem_create_selection (private))) (mode) (base) (count) (size) (caller_frame)) output ) ”
.

Definition OSMemCreate_which_implies_wit_7_split_goal_2 := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (pmem: Z) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mem_create_reservation sg base count size entry private post )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (UCOS2_state_inv sg (replace_MemoryS (post) (entry)) ) ”
.

Definition OSMemCreate_which_implies_wit_7_split_goal_spatial := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (private: MemoryPrivatePartition) (post: GlobMemoryState) (pmem: Z) (PreH1 : (( &( "OSMemFreeList" ) ) = (g_OSMemFreeList (sg)))) (PreH2 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH3 : (mem_create_profile sg )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (mem_create_reservation sg base count size entry private post )) (PreH6 : (mem_create_byte_access (mem_create_entry_resources (sg) (entry) (mode) (base) (count) (size) (caller_frame)) output )) ,
  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  (mem_create_head_field_frame sg entry private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  (UCOS2_inv sg (replace_MemoryS (post) (entry)) )
  **  (memory_private_control_rep sg private )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
.

Definition OSMemCreate_which_implies_wit_8 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (pmem: Z) (PreH1 : (pmem = 0)) (PreH2 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH3 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH4 : (critical_region_interval critical sg invocation checkpoint current )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  “ (pmem = 0) ” 
  &&  “ (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (0) (90)) current ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((output) # UChar  |->_)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (current) (caller_frame)) output )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (pmem: Z) (PreH1 : (pmem = 0)) (PreH2 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH3 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH4 : (critical_region_interval critical sg invocation checkpoint current )) (PreH5 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH6 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (x: Z) ,
  “ (pmem = 0) ” 
  &&  “ (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (0) (90)) current ) ”
  &&  ((output) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (0) (current) (caller_frame)) output )
).

Definition OSMemCreate_which_implies_wit_9 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (pmem: Z) (PreH1 : (pmem <> 0)) (PreH2 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH3 : (mem_create_profile sg )) (PreH4 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH5 : (critical_region_interval critical sg invocation checkpoint current )) (PreH6 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) (PreH9 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (private: MemoryPrivatePartition) ,
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ”
  &&  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private 0 caller_frame X )
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State) (current: UCOS2_Verify_State) (pmem: Z) (PreH1 : (pmem <> 0)) (PreH2 : (pmem = (mem_create_selected_pointer (sg) (selected)))) (PreH3 : (mem_create_profile sg )) (PreH4 : (mem_create_acquire_facts critical sg invocation mode base count size before entry selected checkpoint )) (PreH5 : (critical_region_interval critical sg invocation checkpoint current )) (PreH6 : (mem_create_call_domain critical sg invocation mode base count size before )) (PreH7 : (mem_create_output_rely critical sg invocation mode base count size output caller_frame )) (PreH8 : (mem_create_byte_access (mem_create_detached_resources (sg) (checkpoint) (selected) (mode) (base) (count) (size) (caller_frame)) output )) (PreH9 : (mem_create_safe critical sg invocation base count size output before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (mem_create_selected_resources sg selected )
  **  (mem_create_input_resources mode base count size )
  **  (caller_frame )
|--
  EX (private: MemoryPrivatePartition) ,
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mode = MemCreateArena) ” 
  &&  “ ((memPrivateBase (private)) = base) ” 
  &&  “ ((memPrivateBlockCount (private)) = count) ” 
  &&  “ ((memPrivateBlockSize (private)) = size) ” 
  &&  “ (memory_private_initialization_valid private ) ”
  &&  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private 0 caller_frame X )
).

Definition OSMemCreate_which_implies_wit_10 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (i: Z) (plink: Z) (pblk: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (count - 1 ))) (PreH3 : (plink = (base + (i * size ) ))) (PreH4 : (pblk = (base + ((i + 1 ) * size ) ))) (PreH5 : ((memPrivateBase (private)) = base)) (PreH6 : ((memPrivateBlockCount (private)) = count)) (PreH7 : ((memPrivateBlockSize (private)) = size)) (PreH8 : (memory_private_initialization_valid private )) ,
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
|--
  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ (pblk = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((plink) # Ptr  |->_)
  **  (mem_create_loop_resources sg current private i caller_frame )
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (i: Z) (plink: Z) (pblk: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (count - 1 ))) (PreH3 : (plink = (base + (i * size ) ))) (PreH4 : (pblk = (base + ((i + 1 ) * size ) ))) (PreH5 : ((memPrivateBase (private)) = base)) (PreH6 : ((memPrivateBlockCount (private)) = count)) (PreH7 : ((memPrivateBlockSize (private)) = size)) (PreH8 : (memory_private_initialization_valid private )) ,
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
|--
  EX (x: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < (count - 1 )) ” 
  &&  “ (plink = (base + (i * size ) )) ” 
  &&  “ (pblk = (base + ((i + 1 ) * size ) )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) ((i + 1 )) (caller_frame)) output ) ”
  &&  ((plink) # Ptr  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_loop_resources sg current private i caller_frame )
).

Definition OSMemCreate_which_implies_wit_11 := 
(
forall (caller_frame: Assertion) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (i: Z) (pblk: Z) (PreH1 : (plink = (base + (i * size ) ))) (PreH2 : (pblk = (base + ((i + 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (0 <= i)) (PreH8 : (i < (count - 1 ))) ,
  ((plink) # Ptr  |-> pblk)
  **  (mem_create_loop_resources sg current private i caller_frame )
|--
  “ (plink = (base + (i * size ) )) ” 
  &&  “ (pblk = (base + ((i + 1 ) * size ) )) ”
  &&  (mem_create_cursor_resources sg current private (i + 1 ) caller_frame )
) \/
(
forall (caller_frame: Assertion) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (i: Z) (pblk: Z) (PreH1 : (plink = (base + (i * size ) ))) (PreH2 : (pblk = (base + ((i + 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (0 <= i)) (PreH8 : (i < (count - 1 ))) ,
  ((plink) # Ptr  |-> pblk)
  **  (mem_create_loop_resources sg current private i caller_frame )
|--
  (mem_create_cursor_resources sg current private (i + 1 ) caller_frame )
).

Definition OSMemCreate_which_implies_wit_11_split_goal_spatial := 
forall (caller_frame: Assertion) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (plink: Z) (i: Z) (pblk: Z) (PreH1 : (plink = (base + (i * size ) ))) (PreH2 : (pblk = (base + ((i + 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (0 <= i)) (PreH8 : (i < (count - 1 ))) ,
  ((plink) # Ptr  |-> pblk)
  **  (mem_create_loop_resources sg current private i caller_frame )
|--
  (mem_create_cursor_resources sg current private (i + 1 ) caller_frame )
.

Definition OSMemCreate_which_implies_wit_12 := 
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (loops: Z) (i: Z) (plink: Z) (PreH1 : (loops = (count - 1 ))) (PreH2 : (i >= loops)) (PreH3 : (i <= (count - 1 ))) (PreH4 : (plink = (base + (i * size ) ))) (PreH5 : ((memPrivateBase (private)) = base)) (PreH6 : ((memPrivateBlockCount (private)) = count)) (PreH7 : ((memPrivateBlockSize (private)) = size)) (PreH8 : (memory_private_initialization_valid private )) ,
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
|--
  “ (i = (count - 1 )) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (plink = (base + ((count - 1 ) * size ) )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((plink) # Ptr  |->_)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
) \/
(
forall (X: (MemCreateOutcome -> (MemCreateWorld -> Prop))) (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (loops: Z) (i: Z) (plink: Z) (PreH1 : (loops = (count - 1 ))) (PreH2 : (i >= loops)) (PreH3 : (i <= (count - 1 ))) (PreH4 : (plink = (base + (i * size ) ))) (PreH5 : ((memPrivateBase (private)) = base)) (PreH6 : ((memPrivateBlockCount (private)) = count)) (PreH7 : ((memPrivateBlockSize (private)) = size)) (PreH8 : (memory_private_initialization_valid private )) ,
  (mem_create_loop_state platform critical sg invocation origin mask base count size output before current private i caller_frame X )
|--
  EX (x: Z) ,
  “ (i = (count - 1 )) ” 
  &&  “ (loops = (count - 1 )) ” 
  &&  “ (plink = (base + ((count - 1 ) * size ) )) ” 
  &&  “ (mem_create_profile sg ) ” 
  &&  “ (mem_create_private_history critical sg invocation base count size before current private ) ” 
  &&  “ (mem_create_safe critical sg invocation base count size output before X ) ” 
  &&  “ (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output ) ”
  &&  ((plink) # Ptr  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
).

Definition OSMemCreate_which_implies_wit_13 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (pmem: Z) (plink: Z) (PreH1 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (plink = (base + ((count - 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) ,
  ((plink) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
|--
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (plink = (base + ((count - 1 ) * size ) )) ” 
  &&  “ (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output ) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (pmem: Z) (plink: Z) (PreH1 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (plink = (base + ((count - 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) ,
  ((plink) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
|--
  “ (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output ) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
).

Definition OSMemCreate_which_implies_wit_13_split_goal_1 := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (pmem: Z) (plink: Z) (PreH1 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (plink = (base + ((count - 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) ,
  ((plink) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
|--
  “ (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output ) ”
.

Definition OSMemCreate_which_implies_wit_13_split_goal_spatial := 
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (sg: StableGlobVars) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (pmem: Z) (plink: Z) (PreH1 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (plink = (base + ((count - 1 ) * size ) ))) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_byte_access (mem_create_cursor_resources (sg) (current) (private) (count) (caller_frame)) output )) ,
  ((plink) # Ptr  |-> 0)
  **  (mem_create_loop_resources sg current private (count - 1 ) caller_frame )
|--
  ((&((pmem)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> (memImageBase ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> (memImageSize ((memPrivateImage (private)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
.

Definition OSMemCreate_which_implies_wit_14 := 
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (pmem: Z) (PreH1 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH2 : (mode = MemCreateArena)) (PreH3 : ((memPrivateBase (private)) = base)) (PreH4 : ((memPrivateBlockCount (private)) = count)) (PreH5 : ((memPrivateBlockSize (private)) = size)) (PreH6 : (memory_private_initialization_valid private )) (PreH7 : (mem_create_profile sg )) (PreH8 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH9 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> base)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> base)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> count)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> count)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> size)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
|--
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (pmem) (0)) (mem_create_publish_state (current) (private)) ) ”
  &&  ((output) # UChar  |->_)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (pmem) ((mem_create_publish_state (current) (private))) (caller_frame)) output )
) \/
(
forall (caller_frame: Assertion) (output: Z) (size: Z) (count: Z) (base: Z) (mode: MemCreateInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (private: MemoryPrivatePartition) (pmem: Z) (PreH1 : (size <= UINT_MAX)) (PreH2 : (count <= UINT_MAX)) (PreH3 : (size >= 0)) (PreH4 : (count >= 0)) (PreH5 : (pmem = (memory_control_addr (sg) ((memPrivateSlot (private)))))) (PreH6 : (mode = MemCreateArena)) (PreH7 : ((memPrivateBase (private)) = base)) (PreH8 : ((memPrivateBlockCount (private)) = count)) (PreH9 : ((memPrivateBlockSize (private)) = size)) (PreH10 : (memory_private_initialization_valid private )) (PreH11 : (mem_create_profile sg )) (PreH12 : (mem_create_private_history critical sg invocation base count size before current private )) (PreH13 : (mem_create_byte_access (mem_create_initialized_resources (sg) (current) (private) (caller_frame)) output )) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemAddr")) # Ptr  |-> base)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> base)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> count)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> count)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemBlkSize")) # UInt  |-> size)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName ((memPrivateImage (private)))))
  **  (mem_create_control_write_frame sg current private caller_frame )
|--
  EX (x: Z) ,
  “ (pmem = (memory_control_addr (sg) ((memPrivateSlot (private))))) ” 
  &&  “ (mem_create_kernel_program critical sg invocation base count size before (mem_create_outcome (pmem) (0)) (mem_create_publish_state (current) (private)) ) ”
  &&  ((output) # UChar  |-> x)
  **  (mem_create_output_residual (mem_create_return_resources (sg) (mode) (base) (count) (size) (pmem) ((mem_create_publish_state (current) (private))) (caller_frame)) output )
).

Module Type VC_Correct.


Axiom proof_of_OSMemCreate_safety_wit_1 : OSMemCreate_safety_wit_1.
Axiom proof_of_OSMemCreate_safety_wit_2 : OSMemCreate_safety_wit_2.
Axiom proof_of_OSMemCreate_safety_wit_3 : OSMemCreate_safety_wit_3.
Axiom proof_of_OSMemCreate_safety_wit_4 : OSMemCreate_safety_wit_4.
Axiom proof_of_OSMemCreate_safety_wit_5 : OSMemCreate_safety_wit_5.
Axiom proof_of_OSMemCreate_safety_wit_6 : OSMemCreate_safety_wit_6.
Axiom proof_of_OSMemCreate_safety_wit_7 : OSMemCreate_safety_wit_7.
Axiom proof_of_OSMemCreate_safety_wit_8 : OSMemCreate_safety_wit_8.
Axiom proof_of_OSMemCreate_safety_wit_9 : OSMemCreate_safety_wit_9.
Axiom proof_of_OSMemCreate_safety_wit_10 : OSMemCreate_safety_wit_10.
Axiom proof_of_OSMemCreate_safety_wit_11 : OSMemCreate_safety_wit_11.
Axiom proof_of_OSMemCreate_entail_wit_1 : OSMemCreate_entail_wit_1.
Axiom proof_of_OSMemCreate_entail_wit_2 : OSMemCreate_entail_wit_2.
Axiom proof_of_OSMemCreate_entail_wit_3 : OSMemCreate_entail_wit_3.
Axiom proof_of_OSMemCreate_entail_wit_4_1 : OSMemCreate_entail_wit_4_1.
Axiom proof_of_OSMemCreate_entail_wit_4_2 : OSMemCreate_entail_wit_4_2.
Axiom proof_of_OSMemCreate_entail_wit_5 : OSMemCreate_entail_wit_5.
Axiom proof_of_OSMemCreate_entail_wit_6 : OSMemCreate_entail_wit_6.
Axiom proof_of_OSMemCreate_return_wit_1 : OSMemCreate_return_wit_1.
Axiom proof_of_OSMemCreate_return_wit_2 : OSMemCreate_return_wit_2.
Axiom proof_of_OSMemCreate_return_wit_3 : OSMemCreate_return_wit_3.
Axiom proof_of_OSMemCreate_return_wit_4 : OSMemCreate_return_wit_4.
Axiom proof_of_OSMemCreate_return_wit_5 : OSMemCreate_return_wit_5.
Axiom proof_of_OSMemCreate_return_wit_6 : OSMemCreate_return_wit_6.
Axiom proof_of_OSMemCreate_partial_solve_wit_1_pure : OSMemCreate_partial_solve_wit_1_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_1 : OSMemCreate_partial_solve_wit_1.
Axiom proof_of_OSMemCreate_partial_solve_wit_2_pure : OSMemCreate_partial_solve_wit_2_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_2 : OSMemCreate_partial_solve_wit_2.
Axiom proof_of_OSMemCreate_partial_solve_wit_3_pure : OSMemCreate_partial_solve_wit_3_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_3 : OSMemCreate_partial_solve_wit_3.
Axiom proof_of_OSMemCreate_partial_solve_wit_4_pure : OSMemCreate_partial_solve_wit_4_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_4 : OSMemCreate_partial_solve_wit_4.
Axiom proof_of_OSMemCreate_partial_solve_wit_5 : OSMemCreate_partial_solve_wit_5.
Axiom proof_of_OSMemCreate_partial_solve_wit_6_pure : OSMemCreate_partial_solve_wit_6_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_6 : OSMemCreate_partial_solve_wit_6.
Axiom proof_of_OSMemCreate_partial_solve_wit_7_pure : OSMemCreate_partial_solve_wit_7_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_7 : OSMemCreate_partial_solve_wit_7.
Axiom proof_of_OSMemCreate_partial_solve_wit_8_pure : OSMemCreate_partial_solve_wit_8_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_8 : OSMemCreate_partial_solve_wit_8.
Axiom proof_of_OSMemCreate_partial_solve_wit_9 : OSMemCreate_partial_solve_wit_9.
Axiom proof_of_OSMemCreate_partial_solve_wit_10_pure : OSMemCreate_partial_solve_wit_10_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_10 : OSMemCreate_partial_solve_wit_10.
Axiom proof_of_OSMemCreate_partial_solve_wit_11_pure : OSMemCreate_partial_solve_wit_11_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_11 : OSMemCreate_partial_solve_wit_11.
Axiom proof_of_OSMemCreate_partial_solve_wit_12_pure : OSMemCreate_partial_solve_wit_12_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_12 : OSMemCreate_partial_solve_wit_12.
Axiom proof_of_OSMemCreate_partial_solve_wit_13_pure : OSMemCreate_partial_solve_wit_13_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_13 : OSMemCreate_partial_solve_wit_13.
Axiom proof_of_OSMemCreate_partial_solve_wit_14_pure : OSMemCreate_partial_solve_wit_14_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_14 : OSMemCreate_partial_solve_wit_14.
Axiom proof_of_OSMemCreate_partial_solve_wit_15_pure : OSMemCreate_partial_solve_wit_15_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_15 : OSMemCreate_partial_solve_wit_15.
Axiom proof_of_OSMemCreate_partial_solve_wit_16_pure : OSMemCreate_partial_solve_wit_16_pure.
Axiom proof_of_OSMemCreate_partial_solve_wit_16 : OSMemCreate_partial_solve_wit_16.
Axiom proof_of_OSMemCreate_which_implies_wit_1 : OSMemCreate_which_implies_wit_1.
Axiom proof_of_OSMemCreate_which_implies_wit_2 : OSMemCreate_which_implies_wit_2.
Axiom proof_of_OSMemCreate_which_implies_wit_3 : OSMemCreate_which_implies_wit_3.
Axiom proof_of_OSMemCreate_which_implies_wit_4 : OSMemCreate_which_implies_wit_4.
Axiom proof_of_OSMemCreate_which_implies_wit_5 : OSMemCreate_which_implies_wit_5.
Axiom proof_of_OSMemCreate_which_implies_wit_6 : OSMemCreate_which_implies_wit_6.
Axiom proof_of_OSMemCreate_which_implies_wit_7 : OSMemCreate_which_implies_wit_7.
Axiom proof_of_OSMemCreate_which_implies_wit_8 : OSMemCreate_which_implies_wit_8.
Axiom proof_of_OSMemCreate_which_implies_wit_9 : OSMemCreate_which_implies_wit_9.
Axiom proof_of_OSMemCreate_which_implies_wit_10 : OSMemCreate_which_implies_wit_10.
Axiom proof_of_OSMemCreate_which_implies_wit_11 : OSMemCreate_which_implies_wit_11.
Axiom proof_of_OSMemCreate_which_implies_wit_12 : OSMemCreate_which_implies_wit_12.
Axiom proof_of_OSMemCreate_which_implies_wit_13 : OSMemCreate_which_implies_wit_13.
Axiom proof_of_OSMemCreate_which_implies_wit_14 : OSMemCreate_which_implies_wit_14.

End VC_Correct.
