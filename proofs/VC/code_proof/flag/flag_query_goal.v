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
Require Import Ucos2Verify.VC.code.flag.spec.flag_query_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSFlagQuery -----*)

Definition OSFlagQuery_safety_wit_1 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = p)) (PreH2 : (perr_pre = error_addr)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagQuery_safety_wit_2 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 110)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagQuery_safety_wit_3 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH5 : (p <> 0)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_query_admission sg p view before observed )) (PreH11 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagQuery_safety_wit_4 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (p <> 0)) (PreH3 : ((flagImageType (observed)) = 5)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH6 : (p <> 0)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_query_admission sg p view before observed )) (PreH12 : (flag_query_safe critical sg invocation p view before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  (flag_query_private_words p view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagQuery_safety_wit_5 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry_2 acquired )) (PreH4 : (p <> 0)) (PreH5 : ((flagImageType (observed)) = 5)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (flag_query_selected view entry_2 acquired )) (PreH9 : (0 <= (flagImageBits (acquired)))) (PreH10 : ((flagImageBits (acquired)) <= 65535)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (p <> 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH16 : (p <> 0)) (PreH17 : (flag_query_admission sg p view before observed )) (PreH18 : (pgrp_pre <> 0)) (PreH19 : (pgrp_pre = p)) (PreH20 : (perr_pre = error_addr)) (PreH21 : (flag_query_admission sg p view before observed )) (PreH22 : (flag_query_safe critical sg invocation p view before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  (flag_query_private_words p view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "flags" ) )) # UShort  |-> (flagImageBits (acquired)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagQuery_return_wit_1 := 
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry_2 acquired )) (PreH4 : (p <> 0)) (PreH5 : ((flagImageType (observed)) = 5)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (flag_query_selected view entry_2 acquired )) (PreH9 : (0 <= (flagImageBits (acquired)))) (PreH10 : ((flagImageBits (acquired)) <= 65535)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (p <> 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH16 : (p <> 0)) (PreH17 : (flag_query_admission sg p view before observed )) (PreH18 : (pgrp_pre <> 0)) (PreH19 : (pgrp_pre = p)) (PreH20 : (perr_pre = error_addr)) (PreH21 : (flag_query_admission sg p view before observed )) (PreH22 : (flag_query_safe critical sg invocation p view before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before (flagImageBits (acquired)) X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry_2 acquired )) (PreH4 : (p <> 0)) (PreH5 : ((flagImageType (observed)) = 5)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (flag_query_selected view entry_2 acquired )) (PreH9 : (0 <= (flagImageBits (acquired)))) (PreH10 : ((flagImageBits (acquired)) <= 65535)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (p <> 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH16 : (p <> 0)) (PreH17 : (flag_query_admission sg p view before observed )) (PreH18 : (pgrp_pre <> 0)) (PreH19 : (pgrp_pre = p)) (PreH20 : (perr_pre = error_addr)) (PreH21 : (flag_query_admission sg p view before observed )) (PreH22 : (flag_query_safe critical sg invocation p view before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before (flagImageBits (acquired)) X )
  **  (caller_frame )
).

Definition OSFlagQuery_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry_2 acquired )) (PreH4 : (p <> 0)) (PreH5 : ((flagImageType (observed)) = 5)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (flag_query_selected view entry_2 acquired )) (PreH9 : (0 <= (flagImageBits (acquired)))) (PreH10 : ((flagImageBits (acquired)) <= 65535)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (p <> 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH16 : (p <> 0)) (PreH17 : (flag_query_admission sg p view before observed )) (PreH18 : (pgrp_pre <> 0)) (PreH19 : (pgrp_pre = p)) (PreH20 : (perr_pre = error_addr)) (PreH21 : (flag_query_admission sg p view before observed )) (PreH22 : (flag_query_safe critical sg invocation p view before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before (flagImageBits (acquired)) X )
  **  (caller_frame )
.

Definition OSFlagQuery_return_wit_2 := 
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH5 : (p <> 0)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_query_admission sg p view before observed )) (PreH11 : (flag_query_safe critical sg invocation p view before X )) ,
  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before 0 X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH5 : (p <> 0)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_query_admission sg p view before observed )) (PreH11 : (flag_query_safe critical sg invocation p view before X )) ,
  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before 0 X )
  **  (caller_frame )
).

Definition OSFlagQuery_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH5 : (p <> 0)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_query_admission sg p view before observed )) (PreH11 : (flag_query_safe critical sg invocation p view before X )) ,
  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before 0 X )
  **  (caller_frame )
.

Definition OSFlagQuery_return_wit_3 := 
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : (flag_query_safe critical sg invocation p view before X )) ,
  ((perr_pre) # UChar  |-> 110)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before 0 X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : (flag_query_safe critical sg invocation p view before X )) ,
  ((perr_pre) # UChar  |-> 110)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before 0 X )
  **  (caller_frame )
).

Definition OSFlagQuery_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : (flag_query_safe critical sg invocation p view before X )) ,
  ((perr_pre) # UChar  |-> 110)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  (flag_query_api_post platform critical sg invocation origin mask p error_addr view before 0 X )
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ”
.

Definition OSFlagQuery_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = p)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  (flag_query_resources platform critical sg invocation origin mask p view before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_1 := OSFlagQuery_partial_solve_wit_1_pure -> OSFlagQuery_partial_solve_wit_1_aux.

Definition OSFlagQuery_partial_solve_wit_2_pure := 
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (p <> 0)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = p)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((flagImageType (observed)) <> 5) ”
) \/
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH4 : (p <> 0)) (PreH5 : (flag_query_admission sg p view before observed )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_query_admission sg p view before observed )) (PreH10 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) <> 5) ”
).

Definition OSFlagQuery_partial_solve_wit_2_pure_split_goal_1 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH4 : (p <> 0)) (PreH5 : (flag_query_admission sg p view before observed )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_query_admission sg p view before observed )) (PreH10 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) <> 5) ”
.

Definition OSFlagQuery_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (p <> 0)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = p)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (flag_query_safe critical sg invocation p view before X )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((flagImageType (observed)) <> 5) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_2 := OSFlagQuery_partial_solve_wit_2_pure -> OSFlagQuery_partial_solve_wit_2_aux.

Definition OSFlagQuery_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (p <> 0)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = p)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((flagImageType (observed)) = 5) ”
) \/
(
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (flag_query_admission sg p view before observed )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_query_admission sg p view before observed )) (PreH10 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) = 5) ”
).

Definition OSFlagQuery_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH4 : (p <> 0)) (PreH5 : (flag_query_admission sg p view before observed )) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = p)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_query_admission sg p view before observed )) (PreH10 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) = 5) ”
.

Definition OSFlagQuery_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (p <> 0)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = p)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (flag_query_safe critical sg invocation p view before X )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_3 := OSFlagQuery_partial_solve_wit_3_pure -> OSFlagQuery_partial_solve_wit_3_aux.

Definition OSFlagQuery_partial_solve_wit_4 := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH5 : (p <> 0)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = p)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_query_admission sg p view before observed )) (PreH11 : (flag_query_safe critical sg invocation p view before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (p <> 0)) (PreH3 : ((flagImageType (observed)) = 5)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH6 : (p <> 0)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_query_admission sg p view before observed )) (PreH12 : (flag_query_safe critical sg invocation p view before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  (flag_query_private_words p view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ”
.

Definition OSFlagQuery_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (p <> 0)) (PreH3 : ((flagImageType (observed)) = 5)) (PreH4 : (flag_query_admission sg p view before observed )) (PreH5 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH6 : (p <> 0)) (PreH7 : (flag_query_admission sg p view before observed )) (PreH8 : (pgrp_pre <> 0)) (PreH9 : (pgrp_pre = p)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (flag_query_admission sg p view before observed )) (PreH12 : (flag_query_safe critical sg invocation p view before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_5 := OSFlagQuery_partial_solve_wit_5_pure -> OSFlagQuery_partial_solve_wit_5_aux.

Definition OSFlagQuery_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH5 : (flag_query_selected view entry acquired )) (PreH6 : (0 <= (flagImageBits (acquired)))) (PreH7 : ((flagImageBits (acquired)) <= 65535)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (p <> 0)) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_query_admission sg p view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (p <> 0)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flag_query_admission sg p view before observed )) (PreH19 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
  **  ((( &( "flags" ) )) # UShort  |-> (flagImageBits (acquired)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_selected view entry acquired ) ”
.

Definition OSFlagQuery_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH5 : (flag_query_selected view entry acquired )) (PreH6 : (0 <= (flagImageBits (acquired)))) (PreH7 : ((flagImageBits (acquired)) <= 65535)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (p <> 0)) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_query_admission sg p view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (p <> 0)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = p)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flag_query_admission sg p view before observed )) (PreH19 : (flag_query_safe critical sg invocation p view before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_selected view entry acquired ) ” 
  &&  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_query_selected view entry acquired ) ” 
  &&  “ (0 <= (flagImageBits (acquired))) ” 
  &&  “ ((flagImageBits (acquired)) <= 65535) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_6 := OSFlagQuery_partial_solve_wit_6_pure -> OSFlagQuery_partial_solve_wit_6_aux.

Definition OSFlagQuery_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry_2 acquired )) (PreH4 : (p <> 0)) (PreH5 : ((flagImageType (observed)) = 5)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (flag_query_selected view entry_2 acquired )) (PreH9 : (0 <= (flagImageBits (acquired)))) (PreH10 : ((flagImageBits (acquired)) <= 65535)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (p <> 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH16 : (p <> 0)) (PreH17 : (flag_query_admission sg p view before observed )) (PreH18 : (pgrp_pre <> 0)) (PreH19 : (pgrp_pre = p)) (PreH20 : (perr_pre = error_addr)) (PreH21 : (flag_query_admission sg p view before observed )) (PreH22 : (flag_query_safe critical sg invocation p view before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> p)
  **  (UCOS2_inv sg entry_2 )
  **  (flag_query_private_words p view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "flags" ) )) # UShort  |-> (flagImageBits (acquired)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (retval = retval) ”
.

Definition OSFlagQuery_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (error_addr: Z) (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry_2 acquired )) (PreH4 : (p <> 0)) (PreH5 : ((flagImageType (observed)) = 5)) (PreH6 : (flag_query_admission sg p view before observed )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (flag_query_selected view entry_2 acquired )) (PreH9 : (0 <= (flagImageBits (acquired)))) (PreH10 : ((flagImageBits (acquired)) <= 65535)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (p <> 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_query_admission sg p view before observed )) (PreH15 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH16 : (p <> 0)) (PreH17 : (flag_query_admission sg p view before observed )) (PreH18 : (pgrp_pre <> 0)) (PreH19 : (pgrp_pre = p)) (PreH20 : (perr_pre = error_addr)) (PreH21 : (flag_query_admission sg p view before observed )) (PreH22 : (flag_query_safe critical sg invocation p view before X )) ,
  (UCOS2_inv sg entry_2 )
  **  (flag_query_private_words p view )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (retval = retval) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_selected view entry_2 acquired ) ” 
  &&  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_query_selected view entry_2 acquired ) ” 
  &&  “ (0 <= (flagImageBits (acquired))) ” 
  &&  “ ((flagImageBits (acquired)) <= 65535) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = p) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_safe critical sg invocation p view before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (flag_query_private_words p view )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagQuery_partial_solve_wit_7 := OSFlagQuery_partial_solve_wit_7_pure -> OSFlagQuery_partial_solve_wit_7_aux.

Definition OSFlagQuery_which_implies_wit_1 := 
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) ,
  (flag_query_resources platform critical sg invocation origin mask p view before )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ”
  &&  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
) \/
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) ,
  (flag_query_resources platform critical sg invocation origin mask p view before )
|--
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
).

Definition OSFlagQuery_which_implies_wit_1_split_goal_spatial := 
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) ,
  (flag_query_resources platform critical sg invocation origin mask p view before )
|--
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
.

Definition OSFlagQuery_which_implies_wit_2 := 
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
|--
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) <> 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ”
  &&  (flag_query_resources platform critical sg invocation origin mask p view before )
) \/
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
|--
  (flag_query_resources platform critical sg invocation origin mask p view before )
).

Definition OSFlagQuery_which_implies_wit_2_split_goal_spatial := 
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) <> 5)) (PreH3 : (flag_query_admission sg p view before observed )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
|--
  (flag_query_resources platform critical sg invocation origin mask p view before )
.

Definition OSFlagQuery_which_implies_wit_3 := 
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
|--
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_query_private_words p view )
) \/
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_query_private_words p view )
).

Definition OSFlagQuery_which_implies_wit_3_split_goal_spatial := 
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_query_type_frame platform critical sg invocation origin mask p view before observed )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (flag_query_private_words p view )
.

Definition OSFlagQuery_which_implies_wit_4 := 
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (flag_query_private_words p view )
|--
  EX (acquired: FlagGroupImage)  (entry: UCOS2_Verify_State) ,
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_query_selected view entry acquired ) ” 
  &&  “ (0 <= (flagImageBits (acquired))) ” 
  &&  “ ((flagImageBits (acquired)) <= 65535) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
) \/
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (p <> 0)) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_query_admission sg p view before observed )) (PreH4 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (flag_query_private_words p view )
|--
  EX (acquired: FlagGroupImage)  (entry: UCOS2_Verify_State) ,
  “ (p <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_query_selected view entry acquired ) ” 
  &&  “ (0 <= (flagImageBits (acquired))) ” 
  &&  “ ((flagImageBits (acquired)) <= 65535) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
).

Definition OSFlagQuery_which_implies_wit_5 := 
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry acquired )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
|--
  “ (p <> 0) ” 
  &&  “ (flag_query_admission sg p view before observed ) ” 
  &&  “ (flag_query_selected view entry acquired ) ”
  &&  (UCOS2_inv sg entry )
  **  (flag_query_private_words p view )
) \/
(
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry acquired )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
|--
  (UCOS2_inv sg entry )
  **  (flag_query_private_words p view )
).

Definition OSFlagQuery_which_implies_wit_5_split_goal_spatial := 
forall (p: Z) (observed: FlagGroupImage) (view: FlagQueryView) (before: UCOS2_Verify_State) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (acquired: FlagGroupImage) (PreH1 : (p <> 0)) (PreH2 : (flag_query_admission sg p view before observed )) (PreH3 : (flag_query_selected view entry acquired )) ,
  ((&((p)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (acquired)))
  **  (flag_query_flags_frame sg p view entry acquired )
|--
  (UCOS2_inv sg entry )
  **  (flag_query_private_words p view )
.

Module Type VC_Correct.


Axiom proof_of_OSFlagQuery_safety_wit_1 : OSFlagQuery_safety_wit_1.
Axiom proof_of_OSFlagQuery_safety_wit_2 : OSFlagQuery_safety_wit_2.
Axiom proof_of_OSFlagQuery_safety_wit_3 : OSFlagQuery_safety_wit_3.
Axiom proof_of_OSFlagQuery_safety_wit_4 : OSFlagQuery_safety_wit_4.
Axiom proof_of_OSFlagQuery_safety_wit_5 : OSFlagQuery_safety_wit_5.
Axiom proof_of_OSFlagQuery_return_wit_1 : OSFlagQuery_return_wit_1.
Axiom proof_of_OSFlagQuery_return_wit_2 : OSFlagQuery_return_wit_2.
Axiom proof_of_OSFlagQuery_return_wit_3 : OSFlagQuery_return_wit_3.
Axiom proof_of_OSFlagQuery_partial_solve_wit_1_pure : OSFlagQuery_partial_solve_wit_1_pure.
Axiom proof_of_OSFlagQuery_partial_solve_wit_1 : OSFlagQuery_partial_solve_wit_1.
Axiom proof_of_OSFlagQuery_partial_solve_wit_2_pure : OSFlagQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSFlagQuery_partial_solve_wit_2 : OSFlagQuery_partial_solve_wit_2.
Axiom proof_of_OSFlagQuery_partial_solve_wit_3_pure : OSFlagQuery_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagQuery_partial_solve_wit_3 : OSFlagQuery_partial_solve_wit_3.
Axiom proof_of_OSFlagQuery_partial_solve_wit_4 : OSFlagQuery_partial_solve_wit_4.
Axiom proof_of_OSFlagQuery_partial_solve_wit_5_pure : OSFlagQuery_partial_solve_wit_5_pure.
Axiom proof_of_OSFlagQuery_partial_solve_wit_5 : OSFlagQuery_partial_solve_wit_5.
Axiom proof_of_OSFlagQuery_partial_solve_wit_6_pure : OSFlagQuery_partial_solve_wit_6_pure.
Axiom proof_of_OSFlagQuery_partial_solve_wit_6 : OSFlagQuery_partial_solve_wit_6.
Axiom proof_of_OSFlagQuery_partial_solve_wit_7_pure : OSFlagQuery_partial_solve_wit_7_pure.
Axiom proof_of_OSFlagQuery_partial_solve_wit_7 : OSFlagQuery_partial_solve_wit_7.
Axiom proof_of_OSFlagQuery_which_implies_wit_1 : OSFlagQuery_which_implies_wit_1.
Axiom proof_of_OSFlagQuery_which_implies_wit_2 : OSFlagQuery_which_implies_wit_2.
Axiom proof_of_OSFlagQuery_which_implies_wit_3 : OSFlagQuery_which_implies_wit_3.
Axiom proof_of_OSFlagQuery_which_implies_wit_4 : OSFlagQuery_which_implies_wit_4.
Axiom proof_of_OSFlagQuery_which_implies_wit_5 : OSFlagQuery_which_implies_wit_5.

End VC_Correct.
