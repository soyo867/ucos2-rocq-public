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
Require Import Ucos2Verify.VC.code.flag.spec.flag_name_set_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSFlagNameSet -----*)

Definition OSFlagNameSet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pgrp_pre = p)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (pgrp_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pgrp_pre = p)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (pgrp_pre <> 0)) (PreH6 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = p)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (pgrp_pre <> 0)) (PreH6 : (pname_pre <> 0)) (PreH7 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH8 : (flag_name_set_admission critical sg invocation p name view before )) (PreH9 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = p)) (PreH2 : (pname_pre = name)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (pgrp_pre <> 0)) (PreH6 : (pname_pre <> 0)) (PreH7 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH8 : (flag_name_set_admission critical sg invocation p name view before )) (PreH9 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_name_set_input_rep p view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (flag_name_set_admission critical sg invocation p name view before )) (PreH10 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (flag_name_set_admission critical sg invocation p name view before )) (PreH10 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_name_set_input_rep p view )
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (flag_name_set_admission critical sg invocation p name view before )) (PreH10 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_11 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pname_pre <> 0)) (PreH8 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH9 : (flag_name_set_admission critical sg invocation p name view before )) (PreH10 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_name_set_input_rep p view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_12 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_13 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (flag_name_set_admission critical sg invocation p name view before )) (PreH11 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_14 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (flag_name_set_admission critical sg invocation p name view before )) (PreH11 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_name_set_input_rep p view )
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_15 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH12 : (pgrp_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (flag_name_set_admission critical sg invocation p name view before )) (PreH16 : ((task_name_set_nesting (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_16 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH12 : (pgrp_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (flag_name_set_admission critical sg invocation p name view before )) (PreH16 : ((task_name_set_nesting (before)) = 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  “ False ”
.

Definition OSFlagNameSet_safety_wit_17 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= (task_name_set_nesting (before)))) (PreH7 : ((task_name_set_nesting (before)) <= 255)) (PreH8 : (pname_pre <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = p)) (PreH11 : (pname_pre = name)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH14 : (pgrp_pre <> 0)) (PreH15 : (pname_pre <> 0)) (PreH16 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH17 : (flag_name_set_admission critical sg invocation p name view before )) (PreH18 : ((task_name_set_nesting (before)) = 0)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_18 := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 1 entry )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_safety_wit_19 := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (flag_name_set_update (view) (entry) (image) (name)) )
  **  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameSet_entail_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= (task_name_set_nesting (before)))) (PreH7 : ((task_name_set_nesting (before)) <= 255)) (PreH8 : (pname_pre <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = p)) (PreH11 : (pname_pre = name)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH14 : (pgrp_pre <> 0)) (PreH15 : (pname_pre <> 0)) (PreH16 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH17 : (flag_name_set_admission critical sg invocation p name view before )) (PreH18 : ((task_name_set_nesting (before)) = 0)) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  EX (image: FlagGroupImage)  (entry: UCOS2_Verify_State) ,
  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ (flag_name_set_publication_ready view entry image name ) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= (task_name_set_nesting (before)))) (PreH7 : ((task_name_set_nesting (before)) <= 255)) (PreH8 : (pname_pre <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = p)) (PreH11 : (pname_pre = name)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH14 : (pgrp_pre <> 0)) (PreH15 : (pname_pre <> 0)) (PreH16 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH17 : (flag_name_set_admission critical sg invocation p name view before )) (PreH18 : ((task_name_set_nesting (before)) = 0)) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  EX (x: Z)  (image: FlagGroupImage)  (entry: UCOS2_Verify_State) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ (flag_name_set_publication_ready view entry image name ) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  (caller_frame )
).

Definition OSFlagNameSet_entail_wit_2 := 
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (p <> 0)) (PreH3 : (name <> 0)) (PreH4 : ((task_name_set_nesting (before)) = 0)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (flag_name_set_access sg p view entry image )) (PreH8 : (flag_name_set_publication_ready view entry image name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_name_set_step view name entry 1 entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (p <> 0)) (PreH3 : (name <> 0)) (PreH4 : ((task_name_set_nesting (before)) = 0)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (flag_name_set_access sg p view entry image )) (PreH8 : (flag_name_set_publication_ready view entry image name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  (caller_frame )
|--
  “ (flag_name_set_step view name entry 1 entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (flag_name_set_private_rep p view )
  **  (caller_frame )
).

Definition OSFlagNameSet_entail_wit_2_split_goal_1 := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (p <> 0)) (PreH3 : (name <> 0)) (PreH4 : ((task_name_set_nesting (before)) = 0)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (flag_name_set_access sg p view entry image )) (PreH8 : (flag_name_set_publication_ready view entry image name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  (caller_frame )
|--
  “ (flag_name_set_step view name entry 1 entry ) ”
.

Definition OSFlagNameSet_entail_wit_2_split_goal_spatial := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (p <> 0)) (PreH3 : (name <> 0)) (PreH4 : ((task_name_set_nesting (before)) = 0)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (flag_name_set_access sg p view entry image )) (PreH8 : (flag_name_set_publication_ready view entry image name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  (caller_frame )
|--
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (flag_name_set_private_rep p view )
  **  (caller_frame )
.

Definition OSFlagNameSet_entail_wit_3 := 
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_set_access sg p view entry image )) (PreH2 : ((flagImageType (image)) = 5)) (PreH3 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (name <> 0)) (PreH6 : ((task_name_set_nesting (before)) = 0)) (PreH7 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (flag_name_set_access sg p view entry image )) (PreH10 : (flag_name_set_publication_ready view entry image name )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> name)
  **  (flag_name_set_name_frame sg p view entry image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_set_access sg p view entry image )) (PreH2 : ((flagImageType (image)) = 5)) (PreH3 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (name <> 0)) (PreH6 : ((task_name_set_nesting (before)) = 0)) (PreH7 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (flag_name_set_access sg p view entry image )) (PreH10 : (flag_name_set_publication_ready view entry image name )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> name)
  **  (flag_name_set_name_frame sg p view entry image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller_frame )
|--
  “ (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  (caller_frame )
).

Definition OSFlagNameSet_entail_wit_3_split_goal_1 := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_set_access sg p view entry image )) (PreH2 : ((flagImageType (image)) = 5)) (PreH3 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (name <> 0)) (PreH6 : ((task_name_set_nesting (before)) = 0)) (PreH7 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (flag_name_set_access sg p view entry image )) (PreH10 : (flag_name_set_publication_ready view entry image name )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> name)
  **  (flag_name_set_name_frame sg p view entry image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller_frame )
|--
  “ (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) ) ”
.

Definition OSFlagNameSet_entail_wit_3_split_goal_spatial := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_set_access sg p view entry image )) (PreH2 : ((flagImageType (image)) = 5)) (PreH3 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (name <> 0)) (PreH6 : ((task_name_set_nesting (before)) = 0)) (PreH7 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (flag_name_set_access sg p view entry image )) (PreH10 : (flag_name_set_publication_ready view entry image name )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> name)
  **  (flag_name_set_name_frame sg p view entry image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller_frame )
|--
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  (caller_frame )
.

Definition OSFlagNameSet_return_wit_1 := 
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
) \/
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
).

Definition OSFlagNameSet_return_wit_1_split_goal_spatial := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
.

Definition OSFlagNameSet_return_wit_2 := 
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 1 entry )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
) \/
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 1 entry )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
).

Definition OSFlagNameSet_return_wit_2_split_goal_spatial := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 1 entry )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
.

Definition OSFlagNameSet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) > 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH13 : (pgrp_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (flag_name_set_admission critical sg invocation p name view before )) (PreH17 : ((task_name_set_nesting (before)) > 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |-> 18)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) > 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH13 : (pgrp_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (flag_name_set_admission critical sg invocation p name view before )) (PreH17 : ((task_name_set_nesting (before)) > 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |-> 18)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
).

Definition OSFlagNameSet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) > 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH13 : (pgrp_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (flag_name_set_admission critical sg invocation p name view before )) (PreH17 : ((task_name_set_nesting (before)) > 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |-> 18)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
.

Definition OSFlagNameSet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 12)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 12)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
).

Definition OSFlagNameSet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 12)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
.

Definition OSFlagNameSet_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 110)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 110)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
).

Definition OSFlagNameSet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (pgrp_pre = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |-> 110)
|--
  (flag_name_set_api_post platform critical sg invocation origin mask view p name error_addr before X )
  **  (caller_frame )
.

Definition OSFlagNameSet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (flag_name_set_admission critical sg invocation p name view before )) (PreH11 : ((task_name_set_nesting (before)) = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_name_set_input_rep p view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ”
.

Definition OSFlagNameSet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (flag_name_set_admission critical sg invocation p name view before )) (PreH11 : ((task_name_set_nesting (before)) = 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_name_set_input_rep p view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (flag_name_set_admission critical sg invocation p name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
.

Definition OSFlagNameSet_partial_solve_wit_1 := OSFlagNameSet_partial_solve_wit_1_pure -> OSFlagNameSet_partial_solve_wit_1_aux.

Definition OSFlagNameSet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (flag_name_set_admission critical sg invocation p name view before )) (PreH11 : ((task_name_set_nesting (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ”
.

Definition OSFlagNameSet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (pgrp_pre = p)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pname_pre <> 0)) (PreH9 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH10 : (flag_name_set_admission critical sg invocation p name view before )) (PreH11 : ((task_name_set_nesting (before)) > 0)) ,
  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (flag_name_set_admission critical sg invocation p name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) > 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameSet_partial_solve_wit_2 := OSFlagNameSet_partial_solve_wit_2_pure -> OSFlagNameSet_partial_solve_wit_2_aux.

Definition OSFlagNameSet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH12 : (pgrp_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (flag_name_set_admission critical sg invocation p name view before )) (PreH16 : ((task_name_set_nesting (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSFlagNameSet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH12 : (pgrp_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (flag_name_set_admission critical sg invocation p name view before )) (PreH16 : ((task_name_set_nesting (before)) > 0)) ,
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
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (flag_name_set_admission critical sg invocation p name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) > 0) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameSet_partial_solve_wit_3 := OSFlagNameSet_partial_solve_wit_3_pure -> OSFlagNameSet_partial_solve_wit_3_aux.

Definition OSFlagNameSet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH12 : (pgrp_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (flag_name_set_admission critical sg invocation p name view before )) (PreH16 : ((task_name_set_nesting (before)) = 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSFlagNameSet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH12 : (pgrp_pre <> 0)) (PreH13 : (pname_pre <> 0)) (PreH14 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH15 : (flag_name_set_admission critical sg invocation p name view before )) (PreH16 : ((task_name_set_nesting (before)) = 0)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (flag_name_set_admission critical sg invocation p name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
.

Definition OSFlagNameSet_partial_solve_wit_4 := OSFlagNameSet_partial_solve_wit_4_pure -> OSFlagNameSet_partial_solve_wit_4_aux.

Definition OSFlagNameSet_partial_solve_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : ((task_name_set_nesting (before)) <= 0)) (PreH3 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (task_name_set_nesting (before)))) (PreH6 : ((task_name_set_nesting (before)) <= 255)) (PreH7 : (pname_pre <> 0)) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH13 : (pgrp_pre <> 0)) (PreH14 : (pname_pre <> 0)) (PreH15 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH16 : (flag_name_set_admission critical sg invocation p name view before )) (PreH17 : ((task_name_set_nesting (before)) = 0)) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
|--
  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (flag_name_set_admission critical sg invocation p name view before ) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  ((perr_pre) # UChar  |->_)
  **  (flag_name_set_input_rep p view )
.

Definition OSFlagNameSet_partial_solve_wit_6_pure := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 1 entry )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSFlagNameSet_partial_solve_wit_6_aux := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 1 entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_name_set_step view name entry 1 entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (flag_name_set_private_rep p view )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagNameSet_partial_solve_wit_6 := OSFlagNameSet_partial_solve_wit_6_pure -> OSFlagNameSet_partial_solve_wit_6_aux.

Definition OSFlagNameSet_partial_solve_wit_7_pure := 
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH2 : (p <> 0)) (PreH3 : (name <> 0)) (PreH4 : ((task_name_set_nesting (before)) = 0)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (flag_name_set_access sg p view entry image )) (PreH8 : (flag_name_set_publication_ready view entry image name )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ ((flagImageType (image)) = 5) ”
) \/
(
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (name <> 0)) (PreH6 : ((task_name_set_nesting (before)) = 0)) (PreH7 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (flag_name_set_access sg p view entry image )) (PreH10 : (flag_name_set_publication_ready view entry image name )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (image)) = 5) ”
).

Definition OSFlagNameSet_partial_solve_wit_7_pure_split_goal_1 := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (name <> 0)) (PreH6 : ((task_name_set_nesting (before)) = 0)) (PreH7 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (flag_name_set_access sg p view entry image )) (PreH10 : (flag_name_set_publication_ready view entry image name )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (image)) = 5) ”
.

Definition OSFlagNameSet_partial_solve_wit_7_aux := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5)) (PreH2 : (p <> 0)) (PreH3 : (name <> 0)) (PreH4 : ((task_name_set_nesting (before)) = 0)) (PreH5 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (flag_name_set_access sg p view entry image )) (PreH8 : (flag_name_set_publication_ready view entry image name )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ ((flagImageType (image)) = 5) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (image))) (32)) = 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ (flag_name_set_publication_ready view entry image name ) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagNameSet_partial_solve_wit_7 := OSFlagNameSet_partial_solve_wit_7_pure -> OSFlagNameSet_partial_solve_wit_7_aux.

Definition OSFlagNameSet_partial_solve_wit_8_pure := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSFlagNameSet_partial_solve_wit_8_aux := 
forall (X: (FlagNameSetResult -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (error_addr: Z) (name: Z) (p: Z) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : (name <> 0)) (PreH3 : ((task_name_set_nesting (before)) = 0)) (PreH4 : (flag_name_set_safe critical sg invocation view p name before X )) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (p <> 0) ” 
  &&  “ (name <> 0) ” 
  &&  “ ((task_name_set_nesting (before)) = 0) ” 
  &&  “ (flag_name_set_safe critical sg invocation view p name before X ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_name_set_step view name entry 0 (flag_name_set_update (view) (entry) (image) (name)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_name_set_update (view) (entry) (image) (name)) )
  **  (flag_name_set_private_rep p (flag_name_set_updated_view (view) (name)) )
  **  ((error_addr) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagNameSet_partial_solve_wit_8 := OSFlagNameSet_partial_solve_wit_8_pure -> OSFlagNameSet_partial_solve_wit_8_aux.

Definition OSFlagNameSet_which_implies_wit_1 := 
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

Definition OSFlagNameSet_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ ((task_name_set_nesting (before)) <= 255) ”
.

Definition OSFlagNameSet_which_implies_wit_1_split_goal_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= (task_name_set_nesting (before))) ”
.

Definition OSFlagNameSet_which_implies_wit_1_split_goal_3 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSFlagNameSet_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
.

Definition OSFlagNameSet_which_implies_wit_2 := 
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

Definition OSFlagNameSet_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSFlagNameSet_which_implies_wit_3 := 
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

Definition OSFlagNameSet_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_set_nesting_address sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSFlagNameSet_which_implies_wit_4 := 
(
forall (p: Z) (view: FlagQueryView) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_set_access sg p view entry image )) (PreH2 : ((flagImageType (image)) = 5)) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
|--
  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ ((flagImageType (image)) = 5) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |->_)
  **  (flag_name_set_name_frame sg p view entry image )
) \/
(
forall (p: Z) (view: FlagQueryView) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_set_access sg p view entry image )) (PreH2 : ((flagImageType (image)) = 5)) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_name_set_type_frame sg p view entry image )
|--
  EX (x: Z) ,
  “ (flag_name_set_access sg p view entry image ) ” 
  &&  “ ((flagImageType (image)) = 5) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> x)
  **  (flag_name_set_name_frame sg p view entry image )
).

Module Type VC_Correct.


Axiom proof_of_OSFlagNameSet_safety_wit_1 : OSFlagNameSet_safety_wit_1.
Axiom proof_of_OSFlagNameSet_safety_wit_2 : OSFlagNameSet_safety_wit_2.
Axiom proof_of_OSFlagNameSet_safety_wit_3 : OSFlagNameSet_safety_wit_3.
Axiom proof_of_OSFlagNameSet_safety_wit_4 : OSFlagNameSet_safety_wit_4.
Axiom proof_of_OSFlagNameSet_safety_wit_5 : OSFlagNameSet_safety_wit_5.
Axiom proof_of_OSFlagNameSet_safety_wit_6 : OSFlagNameSet_safety_wit_6.
Axiom proof_of_OSFlagNameSet_safety_wit_7 : OSFlagNameSet_safety_wit_7.
Axiom proof_of_OSFlagNameSet_safety_wit_8 : OSFlagNameSet_safety_wit_8.
Axiom proof_of_OSFlagNameSet_safety_wit_9 : OSFlagNameSet_safety_wit_9.
Axiom proof_of_OSFlagNameSet_safety_wit_10 : OSFlagNameSet_safety_wit_10.
Axiom proof_of_OSFlagNameSet_safety_wit_11 : OSFlagNameSet_safety_wit_11.
Axiom proof_of_OSFlagNameSet_safety_wit_12 : OSFlagNameSet_safety_wit_12.
Axiom proof_of_OSFlagNameSet_safety_wit_13 : OSFlagNameSet_safety_wit_13.
Axiom proof_of_OSFlagNameSet_safety_wit_14 : OSFlagNameSet_safety_wit_14.
Axiom proof_of_OSFlagNameSet_safety_wit_15 : OSFlagNameSet_safety_wit_15.
Axiom proof_of_OSFlagNameSet_safety_wit_16 : OSFlagNameSet_safety_wit_16.
Axiom proof_of_OSFlagNameSet_safety_wit_17 : OSFlagNameSet_safety_wit_17.
Axiom proof_of_OSFlagNameSet_safety_wit_18 : OSFlagNameSet_safety_wit_18.
Axiom proof_of_OSFlagNameSet_safety_wit_19 : OSFlagNameSet_safety_wit_19.
Axiom proof_of_OSFlagNameSet_entail_wit_1 : OSFlagNameSet_entail_wit_1.
Axiom proof_of_OSFlagNameSet_entail_wit_2 : OSFlagNameSet_entail_wit_2.
Axiom proof_of_OSFlagNameSet_entail_wit_3 : OSFlagNameSet_entail_wit_3.
Axiom proof_of_OSFlagNameSet_return_wit_1 : OSFlagNameSet_return_wit_1.
Axiom proof_of_OSFlagNameSet_return_wit_2 : OSFlagNameSet_return_wit_2.
Axiom proof_of_OSFlagNameSet_return_wit_3 : OSFlagNameSet_return_wit_3.
Axiom proof_of_OSFlagNameSet_return_wit_4 : OSFlagNameSet_return_wit_4.
Axiom proof_of_OSFlagNameSet_return_wit_5 : OSFlagNameSet_return_wit_5.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_1_pure : OSFlagNameSet_partial_solve_wit_1_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_1 : OSFlagNameSet_partial_solve_wit_1.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_2_pure : OSFlagNameSet_partial_solve_wit_2_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_2 : OSFlagNameSet_partial_solve_wit_2.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_3_pure : OSFlagNameSet_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_3 : OSFlagNameSet_partial_solve_wit_3.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_4_pure : OSFlagNameSet_partial_solve_wit_4_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_4 : OSFlagNameSet_partial_solve_wit_4.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_5 : OSFlagNameSet_partial_solve_wit_5.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_6_pure : OSFlagNameSet_partial_solve_wit_6_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_6 : OSFlagNameSet_partial_solve_wit_6.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_7_pure : OSFlagNameSet_partial_solve_wit_7_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_7 : OSFlagNameSet_partial_solve_wit_7.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_8_pure : OSFlagNameSet_partial_solve_wit_8_pure.
Axiom proof_of_OSFlagNameSet_partial_solve_wit_8 : OSFlagNameSet_partial_solve_wit_8.
Axiom proof_of_OSFlagNameSet_which_implies_wit_1 : OSFlagNameSet_which_implies_wit_1.
Axiom proof_of_OSFlagNameSet_which_implies_wit_2 : OSFlagNameSet_which_implies_wit_2.
Axiom proof_of_OSFlagNameSet_which_implies_wit_3 : OSFlagNameSet_which_implies_wit_3.
Axiom proof_of_OSFlagNameSet_which_implies_wit_4 : OSFlagNameSet_which_implies_wit_4.

End VC_Correct.
