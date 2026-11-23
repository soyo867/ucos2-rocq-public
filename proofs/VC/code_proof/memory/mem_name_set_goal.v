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
Require Import Ucos2Verify.VC.code.memory.spec.mem_name_set_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSMemNameSet -----*)

Definition OSMemNameSet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (pmem_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (pname_pre <> 0)) (PreH7 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH9 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (pmem_pre <> 0)) (PreH6 : (pname_pre <> 0)) (PreH7 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH9 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH10 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH10 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH10 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_11 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH10 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_12 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_13 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH11 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_14 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH11 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_15 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pmem_pre = pe)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH12 : (pmem_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH16 : ((task_name_set_nesting (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_16 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pmem_pre = pe)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH12 : (pmem_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH16 : ((task_name_set_nesting (before)) = 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  “ False ”
.

Definition OSMemNameSet_safety_wit_17 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= (task_name_set_nesting (before)))) (PreH7 : ((task_name_set_nesting (before)) <= 255)) (PreH8 : (pname_pre <> 0)) (PreH9 : (pmem_pre <> 0)) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = name)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH14 : (pmem_pre <> 0)) (PreH15 : (pname_pre <> 0)) (PreH16 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH17 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH18 : ((task_name_set_nesting (before)) = 0)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_safety_wit_18 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (mem_name_set_update (view) (entry) (image) (name)) )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameSet_entail_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= (task_name_set_nesting (before)))) (PreH7 : ((task_name_set_nesting (before)) <= 255)) (PreH8 : (pname_pre <> 0)) (PreH9 : (pmem_pre <> 0)) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = name)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH14 : (pmem_pre <> 0)) (PreH15 : (pname_pre <> 0)) (PreH16 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH17 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH18 : ((task_name_set_nesting (before)) = 0)) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  EX (image: MemoryControlImage)  (entry: UCOS2_Verify_State) ,
  “ (pe <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (mem_query_admission critical sg invocation pe view before ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (mem_query_selected view entry image ) ” 
  &&  “ (mem_name_set_name_available view entry name ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_set_field_frame sg pe view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= (task_name_set_nesting (before)))) (PreH7 : ((task_name_set_nesting (before)) <= 255)) (PreH8 : (pname_pre <> 0)) (PreH9 : (pmem_pre <> 0)) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = name)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH14 : (pmem_pre <> 0)) (PreH15 : (pname_pre <> 0)) (PreH16 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH17 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH18 : ((task_name_set_nesting (before)) = 0)) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  EX (x: Z)  (image: MemoryControlImage)  (entry: UCOS2_Verify_State) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (mem_query_admission critical sg invocation pe view before ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (mem_query_selected view entry image ) ” 
  &&  “ (mem_name_set_name_available view entry name ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_set_field_frame sg pe view entry image )
  **  (caller_frame )
).

Definition OSMemNameSet_entail_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_admission critical sg invocation pe view before )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (mem_query_selected view entry image )) (PreH8 : (mem_name_set_name_available view entry name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> name)
  **  (mem_name_set_field_frame sg pe view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (pe <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_admission critical sg invocation pe view before )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (mem_query_selected view entry image )) (PreH8 : (mem_name_set_name_available view entry name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> name)
  **  (mem_name_set_field_frame sg pe view entry image )
  **  (caller_frame )
|--
  “ (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  (caller_frame )
).

Definition OSMemNameSet_entail_wit_2_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_admission critical sg invocation pe view before )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (mem_query_selected view entry image )) (PreH8 : (mem_name_set_name_available view entry name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> name)
  **  (mem_name_set_field_frame sg pe view entry image )
  **  (caller_frame )
|--
  “ (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) ) ”
.

Definition OSMemNameSet_entail_wit_2_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_admission critical sg invocation pe view before )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (mem_query_selected view entry image )) (PreH8 : (mem_name_set_name_available view entry name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> name)
  **  (mem_name_set_field_frame sg pe view entry image )
  **  (caller_frame )
|--
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  (caller_frame )
.

Definition OSMemNameSet_return_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) > 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (pmem_pre = pe)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH13 : (pmem_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH17 : ((task_name_set_nesting (before)) > 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |-> 18)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) > 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (pmem_pre = pe)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH13 : (pmem_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH17 : ((task_name_set_nesting (before)) > 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |-> 18)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
).

Definition OSMemNameSet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) > 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (pmem_pre = pe)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH13 : (pmem_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH17 : ((task_name_set_nesting (before)) > 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |-> 18)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
.

Definition OSMemNameSet_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 12)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 12)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
).

Definition OSMemNameSet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 12)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
.

Definition OSMemNameSet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 96)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 96)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
).

Definition OSMemNameSet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH6 : (pmem_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 96)
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
.

Definition OSMemNameSet_return_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |-> 0)
  **  (caller_frame )
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |-> 0)
  **  (caller_frame )
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
).

Definition OSMemNameSet_return_wit_4_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |-> 0)
  **  (caller_frame )
|--
  (mem_name_set_api_post platform critical sg invocation origin mask view pe name error_addr before X )
  **  (caller_frame )
.

Definition OSMemNameSet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH11 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ”
.

Definition OSMemNameSet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH11 : ((task_name_set_nesting (before)) = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (mem_query_source_rep sg pe view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_set_admission critical sg invocation pe name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
.

Definition OSMemNameSet_partial_solve_wit_1 := OSMemNameSet_partial_solve_wit_1_pure -> OSMemNameSet_partial_solve_wit_1_aux.

Definition OSMemNameSet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH11 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ”
.

Definition OSMemNameSet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH11 : ((task_name_set_nesting (before)) > 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_set_admission critical sg invocation pe name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) > 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemNameSet_partial_solve_wit_2 := OSMemNameSet_partial_solve_wit_2_pure -> OSMemNameSet_partial_solve_wit_2_aux.

Definition OSMemNameSet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pmem_pre = pe)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH12 : (pmem_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH16 : ((task_name_set_nesting (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMemNameSet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pmem_pre = pe)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH12 : (pmem_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH16 : ((task_name_set_nesting (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((task_name_set_nesting (before)) > 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_set_admission critical sg invocation pe name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) > 0) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMemNameSet_partial_solve_wit_3 := OSMemNameSet_partial_solve_wit_3_pure -> OSMemNameSet_partial_solve_wit_3_aux.

Definition OSMemNameSet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pmem_pre = pe)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH12 : (pmem_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH16 : ((task_name_set_nesting (before)) = 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMemNameSet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pmem_pre <> 0)) (PreH8 : (pmem_pre = pe)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH12 : (pmem_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH16 : ((task_name_set_nesting (before)) = 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_set_admission critical sg invocation pe name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
.

Definition OSMemNameSet_partial_solve_wit_4 := OSMemNameSet_partial_solve_wit_4_pure -> OSMemNameSet_partial_solve_wit_4_aux.

Definition OSMemNameSet_partial_solve_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) <= 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (pmem_pre = pe)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH13 : (pmem_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (mem_name_set_admission critical sg invocation pe name view before )) (PreH17 : ((task_name_set_nesting (before)) = 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_set_admission critical sg invocation pe name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mem_query_source_rep sg pe view )
.

Definition OSMemNameSet_partial_solve_wit_6_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMemNameSet_partial_solve_wit_6_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (pe: Z) (view: MemQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: MemoryControlImage) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (mem_name_set_safe critical sg invocation view pe name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (mem_name_set_safe critical sg invocation view pe name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (mem_name_set_step view name entry 0 (mem_name_set_update (view) (entry) (image) (name)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mem_name_set_update (view) (entry) (image) (name)) )
  **  (mem_query_source_rep sg pe (mem_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
.

Definition OSMemNameSet_partial_solve_wit_6 := OSMemNameSet_partial_solve_wit_6_pure -> OSMemNameSet_partial_solve_wit_6_aux.

Definition OSMemNameSet_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
).

Definition OSMemNameSet_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ ((task_name_set_nesting (before)) <= 255) ”
.

Definition OSMemNameSet_which_implies_wit_1_split_goal_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= (task_name_set_nesting (before))) ”
.

Definition OSMemNameSet_which_implies_wit_1_split_goal_3 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMemNameSet_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
.

Definition OSMemNameSet_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSMemNameSet_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMemNameSet_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSMemNameSet_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Module Type VC_Correct.


Axiom proof_of_OSMemNameSet_safety_wit_1 : OSMemNameSet_safety_wit_1.
Axiom proof_of_OSMemNameSet_safety_wit_2 : OSMemNameSet_safety_wit_2.
Axiom proof_of_OSMemNameSet_safety_wit_3 : OSMemNameSet_safety_wit_3.
Axiom proof_of_OSMemNameSet_safety_wit_4 : OSMemNameSet_safety_wit_4.
Axiom proof_of_OSMemNameSet_safety_wit_5 : OSMemNameSet_safety_wit_5.
Axiom proof_of_OSMemNameSet_safety_wit_6 : OSMemNameSet_safety_wit_6.
Axiom proof_of_OSMemNameSet_safety_wit_7 : OSMemNameSet_safety_wit_7.
Axiom proof_of_OSMemNameSet_safety_wit_8 : OSMemNameSet_safety_wit_8.
Axiom proof_of_OSMemNameSet_safety_wit_9 : OSMemNameSet_safety_wit_9.
Axiom proof_of_OSMemNameSet_safety_wit_10 : OSMemNameSet_safety_wit_10.
Axiom proof_of_OSMemNameSet_safety_wit_11 : OSMemNameSet_safety_wit_11.
Axiom proof_of_OSMemNameSet_safety_wit_12 : OSMemNameSet_safety_wit_12.
Axiom proof_of_OSMemNameSet_safety_wit_13 : OSMemNameSet_safety_wit_13.
Axiom proof_of_OSMemNameSet_safety_wit_14 : OSMemNameSet_safety_wit_14.
Axiom proof_of_OSMemNameSet_safety_wit_15 : OSMemNameSet_safety_wit_15.
Axiom proof_of_OSMemNameSet_safety_wit_16 : OSMemNameSet_safety_wit_16.
Axiom proof_of_OSMemNameSet_safety_wit_17 : OSMemNameSet_safety_wit_17.
Axiom proof_of_OSMemNameSet_safety_wit_18 : OSMemNameSet_safety_wit_18.
Axiom proof_of_OSMemNameSet_entail_wit_1 : OSMemNameSet_entail_wit_1.
Axiom proof_of_OSMemNameSet_entail_wit_2 : OSMemNameSet_entail_wit_2.
Axiom proof_of_OSMemNameSet_return_wit_1 : OSMemNameSet_return_wit_1.
Axiom proof_of_OSMemNameSet_return_wit_2 : OSMemNameSet_return_wit_2.
Axiom proof_of_OSMemNameSet_return_wit_3 : OSMemNameSet_return_wit_3.
Axiom proof_of_OSMemNameSet_return_wit_4 : OSMemNameSet_return_wit_4.
Axiom proof_of_OSMemNameSet_partial_solve_wit_1_pure : OSMemNameSet_partial_solve_wit_1_pure.
Axiom proof_of_OSMemNameSet_partial_solve_wit_1 : OSMemNameSet_partial_solve_wit_1.
Axiom proof_of_OSMemNameSet_partial_solve_wit_2_pure : OSMemNameSet_partial_solve_wit_2_pure.
Axiom proof_of_OSMemNameSet_partial_solve_wit_2 : OSMemNameSet_partial_solve_wit_2.
Axiom proof_of_OSMemNameSet_partial_solve_wit_3_pure : OSMemNameSet_partial_solve_wit_3_pure.
Axiom proof_of_OSMemNameSet_partial_solve_wit_3 : OSMemNameSet_partial_solve_wit_3.
Axiom proof_of_OSMemNameSet_partial_solve_wit_4_pure : OSMemNameSet_partial_solve_wit_4_pure.
Axiom proof_of_OSMemNameSet_partial_solve_wit_4 : OSMemNameSet_partial_solve_wit_4.
Axiom proof_of_OSMemNameSet_partial_solve_wit_5 : OSMemNameSet_partial_solve_wit_5.
Axiom proof_of_OSMemNameSet_partial_solve_wit_6_pure : OSMemNameSet_partial_solve_wit_6_pure.
Axiom proof_of_OSMemNameSet_partial_solve_wit_6 : OSMemNameSet_partial_solve_wit_6.
Axiom proof_of_OSMemNameSet_which_implies_wit_1 : OSMemNameSet_which_implies_wit_1.
Axiom proof_of_OSMemNameSet_which_implies_wit_2 : OSMemNameSet_which_implies_wit_2.
Axiom proof_of_OSMemNameSet_which_implies_wit_3 : OSMemNameSet_which_implies_wit_3.

End VC_Correct.
