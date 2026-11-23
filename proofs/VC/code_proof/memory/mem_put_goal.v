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
Require Import Ucos2Verify.VC.code.memory.spec.mem_put_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSMemPut -----*)

Definition OSMemPut_safety_wit_1 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_put_profile sg )) (PreH2 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH3 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemPut_safety_wit_2 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (mem_put_profile sg )) (PreH3 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH4 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemPut_safety_wit_3 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (pblk_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (mem_put_profile sg )) (PreH8 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH9 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemPut_safety_wit_4 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH7 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (pblk_pre <> 0)) (PreH16 : (pmem_pre <> 0)) (PreH17 : (mem_put_profile sg )) (PreH18 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH19 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemPut_safety_wit_5 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_put_checkpoint (entry) (input) (acquired)) after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH4 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH6 : (mem_put_current_allocation input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH10 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH11 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH12 : (mem_put_profile sg )) (PreH13 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH14 : (critical_region_interval critical sg invocation before entry )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pblk_pre <> 0)) (PreH19 : (pmem_pre <> 0)) (PreH20 : (mem_put_profile sg )) (PreH21 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH22 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemPut_return_wit_1 := 
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_put_checkpoint (entry) (input) (acquired)) after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH4 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH6 : (mem_put_current_allocation input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH10 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH11 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH12 : (mem_put_profile sg )) (PreH13 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH14 : (critical_region_interval critical sg invocation before entry )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pblk_pre <> 0)) (PreH19 : (pmem_pre <> 0)) (PreH20 : (mem_put_profile sg )) (PreH21 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH22 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 0 X )
) \/
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_put_checkpoint (entry) (input) (acquired)) after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH4 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH6 : (mem_put_current_allocation input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH10 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH11 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH12 : (mem_put_profile sg )) (PreH13 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH14 : (critical_region_interval critical sg invocation before entry )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pblk_pre <> 0)) (PreH19 : (pmem_pre <> 0)) (PreH20 : (mem_put_profile sg )) (PreH21 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH22 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 0 X )
).

Definition OSMemPut_return_wit_1_split_goal_spatial := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (mem_put_checkpoint (entry) (input) (acquired)) after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH4 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH6 : (mem_put_current_allocation input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH10 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH11 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH12 : (mem_put_profile sg )) (PreH13 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH14 : (critical_region_interval critical sg invocation before entry )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pblk_pre <> 0)) (PreH19 : (pmem_pre <> 0)) (PreH20 : (mem_put_profile sg )) (PreH21 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH22 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 0 X )
.

Definition OSMemPut_return_wit_2 := 
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH7 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (pblk_pre <> 0)) (PreH16 : (pmem_pre <> 0)) (PreH17 : (mem_put_profile sg )) (PreH18 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH19 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 94 X )
) \/
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH7 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (pblk_pre <> 0)) (PreH16 : (pmem_pre <> 0)) (PreH17 : (mem_put_profile sg )) (PreH18 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH19 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 94 X )
).

Definition OSMemPut_return_wit_2_split_goal_spatial := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH7 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (pblk_pre <> 0)) (PreH16 : (pmem_pre <> 0)) (PreH17 : (mem_put_profile sg )) (PreH18 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH19 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 94 X )
.

Definition OSMemPut_return_wit_3 := 
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pblk_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_put_profile sg )) (PreH4 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH5 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 95 X )
) \/
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pblk_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_put_profile sg )) (PreH4 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH5 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 95 X )
).

Definition OSMemPut_return_wit_3_split_goal_spatial := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pblk_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_put_profile sg )) (PreH4 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH5 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 95 X )
.

Definition OSMemPut_return_wit_4 := 
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (mem_put_profile sg )) (PreH3 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH4 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 96 X )
) \/
(
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (mem_put_profile sg )) (PreH3 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH4 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 96 X )
).

Definition OSMemPut_return_wit_4_split_goal_spatial := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (mem_put_profile sg )) (PreH3 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH4 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  (mem_put_api_post platform critical sg invocation origin mask before pmem_pre pblk_pre input 96 X )
.

Definition OSMemPut_partial_solve_wit_1 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pblk_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_put_profile sg )) (PreH4 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH5 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
.

Definition OSMemPut_partial_solve_wit_2 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (pblk_pre <> 0)) (PreH3 : (pmem_pre <> 0)) (PreH4 : (mem_put_profile sg )) (PreH5 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH6 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
.

Definition OSMemPut_partial_solve_wit_3_pure := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (pblk_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (mem_put_profile sg )) (PreH8 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH9 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ”
.

Definition OSMemPut_partial_solve_wit_3_aux := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (pblk_pre <> 0)) (PreH6 : (pmem_pre <> 0)) (PreH7 : (mem_put_profile sg )) (PreH8 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH9 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (UCOS2_inv sg entry )
  **  (mem_put_input_resources sg pmem_pre pblk_pre input )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemPut_partial_solve_wit_3 := OSMemPut_partial_solve_wit_3_pure -> OSMemPut_partial_solve_wit_3_aux.

Definition OSMemPut_partial_solve_wit_4 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_profile sg )) (PreH2 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH3 : (critical_region_interval critical sg invocation before entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pblk_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH11 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemPut_partial_solve_wit_5_pure := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH2 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH4 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (mem_put_profile sg )) (PreH7 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (pblk_pre <> 0)) (PreH13 : (pmem_pre <> 0)) (PreH14 : (mem_put_profile sg )) (PreH15 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH16 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired))))) ”
.

Definition OSMemPut_partial_solve_wit_5_aux := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH2 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH4 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (mem_put_profile sg )) (PreH7 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (pblk_pre <> 0)) (PreH13 : (pmem_pre <> 0)) (PreH14 : (mem_put_profile sg )) (PreH15 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH16 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemPut_partial_solve_wit_5 := OSMemPut_partial_solve_wit_5_pure -> OSMemPut_partial_solve_wit_5_aux.

Definition OSMemPut_partial_solve_wit_6_pure := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH4 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH7 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH8 : (mem_put_profile sg )) (PreH9 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pblk_pre <> 0)) (PreH15 : (pmem_pre <> 0)) (PreH16 : (mem_put_profile sg )) (PreH17 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH18 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  (UCOS2_inv sg entry )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSMemPut_partial_solve_wit_6_aux := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH4 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH7 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH8 : (mem_put_profile sg )) (PreH9 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pblk_pre <> 0)) (PreH15 : (pmem_pre <> 0)) (PreH16 : (mem_put_profile sg )) (PreH17 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH18 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (UCOS2_inv sg entry )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
.

Definition OSMemPut_partial_solve_wit_6 := OSMemPut_partial_solve_wit_6_pure -> OSMemPut_partial_solve_wit_6_aux.

Definition OSMemPut_partial_solve_wit_7 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH4 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH7 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH8 : (mem_put_profile sg )) (PreH9 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pblk_pre <> 0)) (PreH15 : (pmem_pre <> 0)) (PreH16 : (mem_put_profile sg )) (PreH17 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH18 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry entry )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  “ (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 94 entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry entry )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
.

Definition OSMemPut_partial_solve_wit_8_pure := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH2 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH4 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (mem_put_profile sg )) (PreH7 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (pblk_pre <> 0)) (PreH13 : (pmem_pre <> 0)) (PreH14 : (mem_put_profile sg )) (PreH15 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH16 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ”
.

Definition OSMemPut_partial_solve_wit_8_aux := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH2 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH4 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH6 : (mem_put_profile sg )) (PreH7 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (pblk_pre <> 0)) (PreH13 : (pmem_pre <> 0)) (PreH14 : (mem_put_profile sg )) (PreH15 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH16 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (mem_put_focus_frame sg entry pmem_pre pblk_pre input acquired )
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemPut_partial_solve_wit_8 := OSMemPut_partial_solve_wit_8_pure -> OSMemPut_partial_solve_wit_8_aux.

Definition OSMemPut_partial_solve_wit_9_pure := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH3 : (mem_put_current_allocation input acquired )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH7 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (pblk_pre <> 0)) (PreH16 : (pmem_pre <> 0)) (PreH17 : (mem_put_profile sg )) (PreH18 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH19 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((pblk_pre) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem_pre input acquired )
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk_pre)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (mem_put_current_allocation input acquired ) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ”
.

Definition OSMemPut_partial_solve_wit_9_aux := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH3 : (mem_put_current_allocation input acquired )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH7 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (mem_put_profile sg )) (PreH10 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH11 : (critical_region_interval critical sg invocation before entry )) (PreH12 : (UCOS2_state_inv sg entry )) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (pblk_pre <> 0)) (PreH16 : (pmem_pre <> 0)) (PreH17 : (mem_put_profile sg )) (PreH18 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH19 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((pblk_pre) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem_pre input acquired )
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk_pre)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (mem_put_current_allocation input acquired ) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (mem_put_current_allocation input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  ((pblk_pre) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk_pre)
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem_pre)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem_pre input acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSMemPut_partial_solve_wit_9 := OSMemPut_partial_solve_wit_9_pure -> OSMemPut_partial_solve_wit_9_aux.

Definition OSMemPut_partial_solve_wit_10_pure := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH2 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (mem_put_current_allocation input acquired )) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH7 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH11 : (mem_put_profile sg )) (PreH12 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pblk_pre <> 0)) (PreH18 : (pmem_pre <> 0)) (PreH19 : (mem_put_profile sg )) (PreH20 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH21 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  ((( &( "pblk" ) )) # Ptr  |-> pblk_pre)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ”
.

Definition OSMemPut_partial_solve_wit_10_aux := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH2 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (mem_put_current_allocation input acquired )) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH7 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH11 : (mem_put_profile sg )) (PreH12 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pblk_pre <> 0)) (PreH18 : (pmem_pre <> 0)) (PreH19 : (mem_put_profile sg )) (PreH20 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH21 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
|--
  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (mem_put_current_allocation input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
.

Definition OSMemPut_partial_solve_wit_10 := OSMemPut_partial_solve_wit_10_pure -> OSMemPut_partial_solve_wit_10_aux.

Definition OSMemPut_partial_solve_wit_11 := 
forall (pblk_pre: Z) (pmem_pre: Z) (X: (MemPutRawResult -> (UCOS2_Verify_State -> Prop))) (input: MemPutInput) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (PreH1 : (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH2 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) (PreH3 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH5 : (mem_put_current_allocation input acquired )) (PreH6 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH7 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH8 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH9 : (0 <= (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) (PreH11 : (mem_put_profile sg )) (PreH12 : (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired )) (PreH13 : (critical_region_interval critical sg invocation before entry )) (PreH14 : (UCOS2_state_inv sg entry )) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pblk_pre <> 0)) (PreH18 : (pmem_pre <> 0)) (PreH19 : (mem_put_profile sg )) (PreH20 : (mem_put_input_protocol critical sg before pmem_pre pblk_pre input )) (PreH21 : (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
|--
  “ (mem_put_completed critical sg invocation before entry pmem_pre pblk_pre input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (mem_put_current_allocation input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem_pre pblk_pre input acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pblk_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_input_protocol critical sg before pmem_pre pblk_pre input ) ” 
  &&  “ (mem_put_safe critical sg invocation pmem_pre pblk_pre input before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem_pre pblk_pre input (mem_put_raw_result (pmem_pre) (pblk_pre) ((mem_put_acquired_image (acquired)))) )
.

Definition OSMemPut_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  emp
).

Definition OSMemPut_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (UCOS2_state_inv sg before )
.

Definition OSMemPut_which_implies_wit_2 := 
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (pblk: Z) (PreH1 : (mem_put_profile sg )) (PreH2 : (pmem <> 0)) (PreH3 : (pblk <> 0)) (PreH4 : (mem_put_input_protocol critical sg before pmem pblk input )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (critical_region_interval critical sg invocation before entry )) ,
  (UCOS2_inv sg entry )
  **  (mem_put_input_resources sg pmem pblk input )
|--
  EX (acquired: MemPutAcquired) ,
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
) \/
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pmem: Z) (pblk: Z) (PreH1 : (mem_put_profile sg )) (PreH2 : (pmem <> 0)) (PreH3 : (pblk <> 0)) (PreH4 : (mem_put_input_protocol critical sg before pmem pblk input )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (critical_region_interval critical sg invocation before entry )) ,
  (UCOS2_inv sg entry )
  **  (mem_put_input_resources sg pmem pblk input )
|--
  EX (acquired: MemPutAcquired) ,
  “ (mem_put_profile sg ) ” 
  &&  “ (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
).

Definition OSMemPut_which_implies_wit_3 := 
forall (acquired: MemPutAcquired) (pmem: Z) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
|--
  “ (0 <= (memImageNFree ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < 4294967296) ” 
  &&  “ (0 <= (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
.

Definition OSMemPut_which_implies_wit_4 := 
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : (mem_put_profile sg )) (PreH2 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH3 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  “ (mem_put_completed critical sg invocation before entry pmem pblk input acquired 94 entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  (UCOS2_inv sg entry )
  **  (mem_put_result_resources sg pmem pblk input (mem_put_raw_result (pmem) (pblk) ((mem_put_acquired_image (acquired)))) )
) \/
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (mem_put_completed critical sg invocation before entry pmem pblk input acquired 94 entry ) ”
  &&  (UCOS2_inv sg entry )
  **  (mem_put_result_resources sg pmem pblk input (mem_put_raw_result (pmem) (pblk) ((mem_put_acquired_image (acquired)))) )
).

Definition OSMemPut_which_implies_wit_4_split_goal_1 := 
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSMemPut_which_implies_wit_4_split_goal_2 := 
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  “ (mem_put_completed critical sg invocation before entry pmem pblk input acquired 94 entry ) ”
.

Definition OSMemPut_which_implies_wit_4_split_goal_spatial := 
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : ((memImageNFree ((mem_put_acquired_image (acquired)))) >= (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> (memImageNFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  (UCOS2_inv sg entry )
  **  (mem_put_result_resources sg pmem pblk input (mem_put_raw_result (pmem) (pblk) ((mem_put_acquired_image (acquired)))) )
.

Definition OSMemPut_which_implies_wit_5 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (interrupt_saved_value mask cpu_sr )) (PreH2 : (UCOS2_state_inv sg entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (interrupt_saved_value mask cpu_sr )) (PreH2 : (UCOS2_state_inv sg entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
).

Definition OSMemPut_which_implies_wit_5_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (interrupt_saved_value mask cpu_sr )) (PreH2 : (UCOS2_state_inv sg entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
.

Definition OSMemPut_which_implies_wit_6 := 
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  EX (old_word: Z) ,
  “ (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (mem_put_current_allocation input acquired ) ”
  &&  ((pblk) # Ptr  |-> old_word)
  **  (mem_put_success_frame sg entry pmem input acquired )
) \/
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH2 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) ,
  (mem_put_focus_frame sg entry pmem pblk input acquired )
|--
  EX (old_word: Z) ,
  “ (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ) ” 
  &&  “ ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired))))) ” 
  &&  “ (mem_put_current_allocation input acquired ) ”
  &&  ((pblk) # Ptr  |-> old_word)
  **  (mem_put_success_frame sg entry pmem input acquired )
).

Definition OSMemPut_which_implies_wit_7 := 
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : (mem_put_profile sg )) (PreH2 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH3 : (mem_put_current_allocation input acquired )) (PreH4 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH5 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH6 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) ,
  ((pblk) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem input acquired )
|--
  “ (mem_put_completed critical sg invocation before entry pmem pblk input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ”
  &&  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem pblk input (mem_put_raw_result (pmem) (pblk) ((mem_put_acquired_image (acquired)))) )
) \/
(
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : (mem_put_current_allocation input acquired )) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) ,
  ((pblk) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem input acquired )
|--
  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ” 
  &&  “ (mem_put_completed critical sg invocation before entry pmem pblk input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) ) ”
  &&  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem pblk input (mem_put_raw_result (pmem) (pblk) ((mem_put_acquired_image (acquired)))) )
).

Definition OSMemPut_which_implies_wit_7_split_goal_1 := 
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : (mem_put_current_allocation input acquired )) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) ,
  ((pblk) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem input acquired )
|--
  “ (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) ) ”
.

Definition OSMemPut_which_implies_wit_7_split_goal_2 := 
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : (mem_put_current_allocation input acquired )) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) ,
  ((pblk) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem input acquired )
|--
  “ (mem_put_completed critical sg invocation before entry pmem pblk input acquired 0 (mem_put_checkpoint (entry) (input) (acquired)) ) ”
.

Definition OSMemPut_which_implies_wit_7_split_goal_spatial := 
forall (input: MemPutInput) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (pblk: Z) (pmem: Z) (PreH1 : ((memImageCount ((mem_put_acquired_image (acquired)))) <= UINT_MAX)) (PreH2 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) <= UINT_MAX)) (PreH3 : ((memImageCount ((mem_put_acquired_image (acquired)))) >= 0)) (PreH4 : (((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ) >= 0)) (PreH5 : (mem_put_profile sg )) (PreH6 : (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired )) (PreH7 : (mem_put_current_allocation input acquired )) (PreH8 : (0 <= (memImageNFree ((mem_put_acquired_image (acquired)))))) (PreH9 : ((memImageNFree ((mem_put_acquired_image (acquired)))) < (memImageCount ((mem_put_acquired_image (acquired)))))) (PreH10 : ((memImageCount ((mem_put_acquired_image (acquired)))) < 4294967296)) ,
  ((pblk) # Ptr  |-> (memImageFree ((mem_put_acquired_image (acquired)))))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> pblk)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNFree")) # UInt  |-> ((memImageNFree ((mem_put_acquired_image (acquired)))) + 1 ))
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemNBlks")) # UInt  |-> (memImageCount ((mem_put_acquired_image (acquired)))))
  **  (mem_put_success_frame sg entry pmem input acquired )
|--
  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
  **  (mem_put_result_resources sg pmem pblk input (mem_put_raw_result (pmem) (pblk) ((mem_put_acquired_image (acquired)))) )
.

Definition OSMemPut_which_implies_wit_8 := 
(
forall (input: MemPutInput) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (cpu_sr: Z) (PreH1 : (interrupt_saved_value mask cpu_sr )) (PreH2 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (mem_put_checkpoint (entry) (input) (acquired)) )
) \/
(
forall (input: MemPutInput) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (cpu_sr: Z) (PreH1 : (interrupt_saved_value mask cpu_sr )) (PreH2 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (mem_put_checkpoint (entry) (input) (acquired)) )
).

Definition OSMemPut_which_implies_wit_8_split_goal_spatial := 
forall (input: MemPutInput) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (acquired: MemPutAcquired) (cpu_sr: Z) (PreH1 : (interrupt_saved_value mask cpu_sr )) (PreH2 : (UCOS2_state_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_put_checkpoint (entry) (input) (acquired)) )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (mem_put_checkpoint (entry) (input) (acquired)) )
.

Module Type VC_Correct.


Axiom proof_of_OSMemPut_safety_wit_1 : OSMemPut_safety_wit_1.
Axiom proof_of_OSMemPut_safety_wit_2 : OSMemPut_safety_wit_2.
Axiom proof_of_OSMemPut_safety_wit_3 : OSMemPut_safety_wit_3.
Axiom proof_of_OSMemPut_safety_wit_4 : OSMemPut_safety_wit_4.
Axiom proof_of_OSMemPut_safety_wit_5 : OSMemPut_safety_wit_5.
Axiom proof_of_OSMemPut_return_wit_1 : OSMemPut_return_wit_1.
Axiom proof_of_OSMemPut_return_wit_2 : OSMemPut_return_wit_2.
Axiom proof_of_OSMemPut_return_wit_3 : OSMemPut_return_wit_3.
Axiom proof_of_OSMemPut_return_wit_4 : OSMemPut_return_wit_4.
Axiom proof_of_OSMemPut_partial_solve_wit_1 : OSMemPut_partial_solve_wit_1.
Axiom proof_of_OSMemPut_partial_solve_wit_2 : OSMemPut_partial_solve_wit_2.
Axiom proof_of_OSMemPut_partial_solve_wit_3_pure : OSMemPut_partial_solve_wit_3_pure.
Axiom proof_of_OSMemPut_partial_solve_wit_3 : OSMemPut_partial_solve_wit_3.
Axiom proof_of_OSMemPut_partial_solve_wit_4 : OSMemPut_partial_solve_wit_4.
Axiom proof_of_OSMemPut_partial_solve_wit_5_pure : OSMemPut_partial_solve_wit_5_pure.
Axiom proof_of_OSMemPut_partial_solve_wit_5 : OSMemPut_partial_solve_wit_5.
Axiom proof_of_OSMemPut_partial_solve_wit_6_pure : OSMemPut_partial_solve_wit_6_pure.
Axiom proof_of_OSMemPut_partial_solve_wit_6 : OSMemPut_partial_solve_wit_6.
Axiom proof_of_OSMemPut_partial_solve_wit_7 : OSMemPut_partial_solve_wit_7.
Axiom proof_of_OSMemPut_partial_solve_wit_8_pure : OSMemPut_partial_solve_wit_8_pure.
Axiom proof_of_OSMemPut_partial_solve_wit_8 : OSMemPut_partial_solve_wit_8.
Axiom proof_of_OSMemPut_partial_solve_wit_9_pure : OSMemPut_partial_solve_wit_9_pure.
Axiom proof_of_OSMemPut_partial_solve_wit_9 : OSMemPut_partial_solve_wit_9.
Axiom proof_of_OSMemPut_partial_solve_wit_10_pure : OSMemPut_partial_solve_wit_10_pure.
Axiom proof_of_OSMemPut_partial_solve_wit_10 : OSMemPut_partial_solve_wit_10.
Axiom proof_of_OSMemPut_partial_solve_wit_11 : OSMemPut_partial_solve_wit_11.
Axiom proof_of_OSMemPut_which_implies_wit_1 : OSMemPut_which_implies_wit_1.
Axiom proof_of_OSMemPut_which_implies_wit_2 : OSMemPut_which_implies_wit_2.
Axiom proof_of_OSMemPut_which_implies_wit_3 : OSMemPut_which_implies_wit_3.
Axiom proof_of_OSMemPut_which_implies_wit_4 : OSMemPut_which_implies_wit_4.
Axiom proof_of_OSMemPut_which_implies_wit_5 : OSMemPut_which_implies_wit_5.
Axiom proof_of_OSMemPut_which_implies_wit_6 : OSMemPut_which_implies_wit_6.
Axiom proof_of_OSMemPut_which_implies_wit_7 : OSMemPut_which_implies_wit_7.
Axiom proof_of_OSMemPut_which_implies_wit_8 : OSMemPut_which_implies_wit_8.

End VC_Correct.
