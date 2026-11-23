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
Require Import Ucos2Verify.VC.code.flag.spec.flag_create_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSFlagCreate -----*)

Definition OSFlagCreate_safety_wit_1 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 16)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_safety_wit_2 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : ((flag_create_depth (before)) <= 0)) (PreH4 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flags_pre = bits)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= 65535)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH12 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_safety_wit_3 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : ((flag_create_depth (before)) <= 0)) (PreH6 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (flags_pre = bits)) (PreH9 : (0 <= bits)) (PreH10 : (bits <= 65535)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH14 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry_2)))
  **  (flag_create_pool_frame sg entry_2 )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry_2)))
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_safety_wit_4 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : ((flag_create_free_head (sg) (entry_2)) = (flag_pool_addr (sg) (id)))) (PreH4 : ((flag_create_free_head (sg) (entry_2)) = (flag_create_free_head (sg) (entry_2)))) (PreH5 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : ((flag_create_depth (before)) <= 0)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (flag_create_slot sg entry_2 id rest old )) (PreH10 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH11 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : ((flag_create_depth (before)) <= 0)) (PreH17 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flags_pre = bits)) (PreH20 : (0 <= bits)) (PreH21 : (bits <= 65535)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH25 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry_2)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (flag_create_fields_frame sg entry_2 id old )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_safety_wit_5 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH2 : (0 <= bits)) (PreH3 : (bits <= 65535)) (PreH4 : ((flag_create_free_head (sg) (entry_2)) = (flag_pool_addr (sg) (id)))) (PreH5 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : ((flag_create_depth (before)) <= 0)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (flag_create_slot sg entry_2 id rest old )) (PreH10 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH11 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : ((flag_create_depth (before)) <= 0)) (PreH17 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flags_pre = bits)) (PreH20 : (0 <= bits)) (PreH21 : (bits <= 65535)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH25 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry_2 id old (LitMap (("?"%string))) )
  **  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry_2)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry_2)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_safety_wit_6 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH4 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry_2)) 0 (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (UCOS2_state_inv sg (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) )) (PreH6 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH7 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : ((flag_create_free_head (sg) (entry_2)) = (flag_pool_addr (sg) (id)))) (PreH11 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : ((flag_create_depth (before)) <= 0)) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH15 : (flag_create_slot sg entry_2 id rest old )) (PreH16 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH17 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH20 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH21 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : ((flag_create_depth (before)) <= 0)) (PreH23 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH24 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH25 : (flags_pre = bits)) (PreH26 : (0 <= bits)) (PreH27 : (bits <= 65535)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH31 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry_2)))
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_safety_wit_7 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 = (flag_create_free_head (sg) (entry_2)))) (PreH4 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) 0 114 entry_2 )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : ((flag_create_free_head (sg) (entry_2)) = 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : ((flag_create_depth (before)) <= 0)) (PreH12 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flags_pre = bits)) (PreH15 : (0 <= bits)) (PreH16 : (bits <= 65535)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH20 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pgrp" ) )) # Ptr  |-> 0)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagCreate_return_wit_1 := 
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH4 : (flag_create_effect sg entry bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry)) 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH6 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : ((flag_create_depth (before)) <= 0)) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (flag_create_slot sg entry id rest old )) (PreH16 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH17 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH20 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH21 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : ((flag_create_depth (before)) <= 0)) (PreH23 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH24 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH25 : (flags_pre = bits)) (PreH26 : (0 <= bits)) (PreH27 : (bits <= 65535)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH31 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (GlobalStrings_missing LitMap literals )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before (flag_create_free_head (sg) (entry)) X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
) \/
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH4 : (flag_create_effect sg entry bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry)) 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH6 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : ((flag_create_depth (before)) <= 0)) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (flag_create_slot sg entry id rest old )) (PreH16 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH17 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH20 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH21 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : ((flag_create_depth (before)) <= 0)) (PreH23 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH24 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH25 : (flags_pre = bits)) (PreH26 : (0 <= bits)) (PreH27 : (bits <= 65535)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH31 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (GlobalStrings_missing LitMap literals )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before (flag_create_free_head (sg) (entry)) X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
).

Definition OSFlagCreate_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH4 : (flag_create_effect sg entry bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry)) 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH6 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : ((flag_create_depth (before)) <= 0)) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (flag_create_slot sg entry id rest old )) (PreH16 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH17 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH20 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH21 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : ((flag_create_depth (before)) <= 0)) (PreH23 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH24 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH25 : (flags_pre = bits)) (PreH26 : (0 <= bits)) (PreH27 : (bits <= 65535)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH31 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  (GlobalStrings_missing LitMap literals )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before (flag_create_free_head (sg) (entry)) X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_return_wit_2 := 
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 = (flag_create_free_head (sg) (entry_2)))) (PreH4 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) 0 114 entry_2 )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : ((flag_create_free_head (sg) (entry_2)) = 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : ((flag_create_depth (before)) <= 0)) (PreH12 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flags_pre = bits)) (PreH15 : (0 <= bits)) (PreH16 : (bits <= 65535)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH20 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((perr_pre) # UChar  |-> 114)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before 0 X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
) \/
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 = (flag_create_free_head (sg) (entry_2)))) (PreH4 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) 0 114 entry_2 )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : ((flag_create_free_head (sg) (entry_2)) = 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : ((flag_create_depth (before)) <= 0)) (PreH12 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flags_pre = bits)) (PreH15 : (0 <= bits)) (PreH16 : (bits <= 65535)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH20 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((perr_pre) # UChar  |-> 114)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before 0 X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
).

Definition OSFlagCreate_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry_2 current )) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 = (flag_create_free_head (sg) (entry_2)))) (PreH4 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) 0 114 entry_2 )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : ((flag_create_free_head (sg) (entry_2)) = 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : ((flag_create_depth (before)) <= 0)) (PreH12 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flags_pre = bits)) (PreH15 : (0 <= bits)) (PreH16 : (bits <= 65535)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH20 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask current )
  **  ((perr_pre) # UChar  |-> 114)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before 0 X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_return_wit_3 := 
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 16)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before 0 X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
) \/
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 16)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before 0 X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
).

Definition OSFlagCreate_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 16)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  (flag_create_api_post platform critical sg invocation origin mask bits (LitMap (("?"%string))) error_addr before 0 X )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flags_pre = bits)) (PreH2 : (0 <= bits)) (PreH3 : (bits <= 65535)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH7 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ”
.

Definition OSFlagCreate_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flags_pre = bits)) (PreH2 : (0 <= bits)) (PreH3 : (bits <= 65535)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH7 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((perr_pre) # UChar  |->_)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_1 := OSFlagCreate_partial_solve_wit_1_pure -> OSFlagCreate_partial_solve_wit_1_aux.

Definition OSFlagCreate_partial_solve_wit_2_pure := 
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flags_pre = bits)) (PreH4 : (0 <= bits)) (PreH5 : (bits <= 65535)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH9 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (0 < (flag_create_depth (before))) ”
) \/
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 < (flag_create_depth (before))) ”
).

Definition OSFlagCreate_partial_solve_wit_2_pure_split_goal_1 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 < (flag_create_depth (before))) ”
.

Definition OSFlagCreate_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flags_pre = bits)) (PreH4 : (0 <= bits)) (PreH5 : (bits <= 65535)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH9 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (0 < (flag_create_depth (before))) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) > 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_2 := OSFlagCreate_partial_solve_wit_2_pure -> OSFlagCreate_partial_solve_wit_2_aux.

Definition OSFlagCreate_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flags_pre = bits)) (PreH4 : (0 <= bits)) (PreH5 : (bits <= 65535)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH9 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ”
) \/
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ ((flag_create_depth (before)) <= 0) ”
).

Definition OSFlagCreate_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ ((flag_create_depth (before)) <= 0) ”
.

Definition OSFlagCreate_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flags_pre = bits)) (PreH4 : (0 <= bits)) (PreH5 : (bits <= 65535)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH9 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_3 := OSFlagCreate_partial_solve_wit_3_pure -> OSFlagCreate_partial_solve_wit_3_aux.

Definition OSFlagCreate_partial_solve_wit_4 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : ((flag_create_depth (before)) <= 0)) (PreH3 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH4 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH5 : (flags_pre = bits)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= 65535)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH11 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : ((flag_create_depth (before)) <= 0)) (PreH4 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flags_pre = bits)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= 65535)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH12 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ”
.

Definition OSFlagCreate_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : ((flag_create_depth (before)) <= 0)) (PreH4 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flags_pre = bits)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= 65535)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH12 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_5 := OSFlagCreate_partial_solve_wit_5_pure -> OSFlagCreate_partial_solve_wit_5_aux.

Definition OSFlagCreate_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH4 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : ((flag_create_depth (before)) <= 0)) (PreH7 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH8 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flags_pre = bits)) (PreH10 : (0 <= bits)) (PreH11 : (bits <= 65535)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH15 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ”
.

Definition OSFlagCreate_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH4 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : ((flag_create_depth (before)) <= 0)) (PreH7 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH8 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flags_pre = bits)) (PreH10 : (0 <= bits)) (PreH11 : (bits <= 65535)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH15 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_6 := OSFlagCreate_partial_solve_wit_6_pure -> OSFlagCreate_partial_solve_wit_6_aux.

Definition OSFlagCreate_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH4 : ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry)))) (PreH5 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : ((flag_create_depth (before)) <= 0)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH9 : (flag_create_slot sg entry id rest old )) (PreH10 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : ((flag_create_depth (before)) <= 0)) (PreH17 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flags_pre = bits)) (PreH20 : (0 <= bits)) (PreH21 : (bits <= 65535)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH25 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (flag_create_fields_frame sg entry id old )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ”
.

Definition OSFlagCreate_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH4 : ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry)))) (PreH5 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : ((flag_create_depth (before)) <= 0)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH9 : (flag_create_slot sg entry id rest old )) (PreH10 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : ((flag_create_depth (before)) <= 0)) (PreH17 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flags_pre = bits)) (PreH20 : (0 <= bits)) (PreH21 : (bits <= 65535)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH25 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (flag_create_fields_frame sg entry id old )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (flag_create_fields_frame sg entry id old )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_7 := OSFlagCreate_partial_solve_wit_7_pure -> OSFlagCreate_partial_solve_wit_7_aux.

Definition OSFlagCreate_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH2 : (0 <= bits)) (PreH3 : (bits <= 65535)) (PreH4 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH5 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : ((flag_create_depth (before)) <= 0)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH9 : (flag_create_slot sg entry id rest old )) (PreH10 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : ((flag_create_depth (before)) <= 0)) (PreH17 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flags_pre = bits)) (PreH20 : (0 <= bits)) (PreH21 : (bits <= 65535)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH25 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
  **  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ”
.

Definition OSFlagCreate_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH2 : (0 <= bits)) (PreH3 : (bits <= 65535)) (PreH4 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH5 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : ((flag_create_depth (before)) <= 0)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH9 : (flag_create_slot sg entry id rest old )) (PreH10 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH11 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : ((flag_create_depth (before)) <= 0)) (PreH17 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : (flags_pre = bits)) (PreH20 : (0 <= bits)) (PreH21 : (bits <= 65535)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH25 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagCreate_partial_solve_wit_8 := OSFlagCreate_partial_solve_wit_8_pure -> OSFlagCreate_partial_solve_wit_8_aux.

Definition OSFlagCreate_partial_solve_wit_9_pure := 
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH2 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH3 : (0 <= bits)) (PreH4 : (bits <= 65535)) (PreH5 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH6 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : ((flag_create_depth (before)) <= 0)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (flag_create_slot sg entry id rest old )) (PreH11 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH12 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH16 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH17 : ((flag_create_depth (before)) <= 0)) (PreH18 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH19 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH20 : (flags_pre = bits)) (PreH21 : (0 <= bits)) (PreH22 : (bits <= 65535)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH25 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH26 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (flag_create_fields_frame sg entry id old )
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap (("?"%string)))) ”
) \/
(
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH4 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH5 : (0 <= bits)) (PreH6 : (bits <= 65535)) (PreH7 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH8 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : ((flag_create_depth (before)) <= 0)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (flag_create_slot sg entry id rest old )) (PreH13 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH14 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH17 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : ((flag_create_depth (before)) <= 0)) (PreH20 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH21 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : (flags_pre = bits)) (PreH23 : (0 <= bits)) (PreH24 : (bits <= 65535)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH27 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH28 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (flag_create_fields_frame sg entry id old )
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap (("?"%string)))) ”
).

Definition OSFlagCreate_partial_solve_wit_9_pure_split_goal_1 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH4 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH5 : (0 <= bits)) (PreH6 : (bits <= 65535)) (PreH7 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH8 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : ((flag_create_depth (before)) <= 0)) (PreH11 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH12 : (flag_create_slot sg entry id rest old )) (PreH13 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH14 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH15 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH16 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH17 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH18 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH19 : ((flag_create_depth (before)) <= 0)) (PreH20 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH21 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : (flags_pre = bits)) (PreH23 : (0 <= bits)) (PreH24 : (bits <= 65535)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH27 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH28 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (flag_create_fields_frame sg entry id old )
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap (("?"%string)))) ”
.

Definition OSFlagCreate_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH2 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH3 : (0 <= bits)) (PreH4 : (bits <= 65535)) (PreH5 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH6 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH7 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH8 : ((flag_create_depth (before)) <= 0)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (flag_create_slot sg entry id rest old )) (PreH11 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH12 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH15 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH16 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH17 : ((flag_create_depth (before)) <= 0)) (PreH18 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH19 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH20 : (flags_pre = bits)) (PreH21 : (0 <= bits)) (PreH22 : (bits <= 65535)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH25 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH26 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (flag_create_fields_frame sg entry id old )
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap (("?"%string)))) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&(((flag_create_free_head (sg) (entry)))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (flag_create_fields_frame sg entry id old )
  **  (GlobalStrings_missing LitMap literals )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagCreate_partial_solve_wit_9 := OSFlagCreate_partial_solve_wit_9_pure -> OSFlagCreate_partial_solve_wit_9_aux.

Definition OSFlagCreate_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry)))) (PreH2 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH3 : (flag_create_effect sg entry bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry)) 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH4 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH6 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH7 : (0 <= bits)) (PreH8 : (bits <= 65535)) (PreH9 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH10 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH11 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH12 : ((flag_create_depth (before)) <= 0)) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH14 : (flag_create_slot sg entry id rest old )) (PreH15 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH16 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH17 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH18 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH20 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH21 : ((flag_create_depth (before)) <= 0)) (PreH22 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flags_pre = bits)) (PreH25 : (0 <= bits)) (PreH26 : (bits <= 65535)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH29 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH30 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "flags" ) )) # UShort  |-> bits)
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
  **  (GlobalStrings_missing LitMap literals )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ”
.

Definition OSFlagCreate_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : ((flag_create_free_head (sg) (entry)) = (flag_create_free_head (sg) (entry)))) (PreH2 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH3 : (flag_create_effect sg entry bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry)) 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH4 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH6 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH7 : (0 <= bits)) (PreH8 : (bits <= 65535)) (PreH9 : ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id)))) (PreH10 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH11 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH12 : ((flag_create_depth (before)) <= 0)) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH14 : (flag_create_slot sg entry id rest old )) (PreH15 : (flag_create_default_name entry (LitMap (("?"%string))) )) (PreH16 : ((flag_create_free_head (sg) (entry)) <> 0)) (PreH17 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH18 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH20 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH21 : ((flag_create_depth (before)) <= 0)) (PreH22 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flags_pre = bits)) (PreH25 : (0 <= bits)) (PreH26 : (bits <= 65535)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH29 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH30 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
  **  (GlobalStrings_missing LitMap literals )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry)) 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = (flag_pool_addr (sg) (id))) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
  **  (GlobalStrings_missing LitMap literals )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagCreate_partial_solve_wit_10 := OSFlagCreate_partial_solve_wit_10_pure -> OSFlagCreate_partial_solve_wit_10_aux.

Definition OSFlagCreate_partial_solve_wit_11 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH3 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry_2)) 0 (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) )) (PreH4 : (UCOS2_state_inv sg (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) )) (PreH5 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH6 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH7 : (0 <= bits)) (PreH8 : (bits <= 65535)) (PreH9 : ((flag_create_free_head (sg) (entry_2)) = (flag_pool_addr (sg) (id)))) (PreH10 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH11 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH12 : ((flag_create_depth (before)) <= 0)) (PreH13 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH14 : (flag_create_slot sg entry_2 id rest old )) (PreH15 : (flag_create_default_name entry_2 (LitMap (("?"%string))) )) (PreH16 : ((flag_create_free_head (sg) (entry_2)) <> 0)) (PreH17 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH18 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH19 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH20 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH21 : ((flag_create_depth (before)) <= 0)) (PreH22 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH23 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH24 : (flags_pre = bits)) (PreH25 : (0 <= bits)) (PreH26 : (bits <= 65535)) (PreH27 : (perr_pre = error_addr)) (PreH28 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH29 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH30 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) )
  **  (GlobalStrings_missing LitMap literals )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ ((flag_create_free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) (flag_create_free_head (sg) (entry_2)) 0 (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ (flag_create_default_name entry_2 (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_default_name entry_2 (LitMap (("?"%string))) ) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ ((flag_create_free_head (sg) (entry_2)) = (flag_pool_addr (sg) (id))) ” 
  &&  “ ((flag_create_free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_slot sg entry_2 id rest old ) ” 
  &&  “ (flag_create_default_name entry_2 (LitMap (("?"%string))) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 (flag_create_checkpoint (entry_2) (bits) ((LitMap (("?"%string))))) )
  **  (GlobalStrings_missing LitMap literals )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagCreate_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((flag_create_free_head (sg) (entry)) = 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH4 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : ((flag_create_depth (before)) <= 0)) (PreH7 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH8 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flags_pre = bits)) (PreH10 : (0 <= bits)) (PreH11 : (bits <= 65535)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH15 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 = 0) ” 
  &&  “ (0 = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ”
.

Definition OSFlagCreate_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((flag_create_free_head (sg) (entry)) = 0)) (PreH2 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH4 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : ((flag_create_depth (before)) <= 0)) (PreH7 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH8 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flags_pre = bits)) (PreH10 : (0 <= bits)) (PreH11 : (bits <= 65535)) (PreH12 : (perr_pre = error_addr)) (PreH13 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH14 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH15 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (0 = 0) ” 
  &&  “ (0 = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> 0)
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> 0)
  **  (flag_create_pool_frame sg entry )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_12 := OSFlagCreate_partial_solve_wit_12_pure -> OSFlagCreate_partial_solve_wit_12_aux.

Definition OSFlagCreate_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (0 = 0)) (PreH2 : (0 = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_effect sg entry bits (LitMap (("?"%string))) 0 114 entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : ((flag_create_free_head (sg) (entry)) = 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : ((flag_create_depth (before)) <= 0)) (PreH11 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flags_pre = bits)) (PreH14 : (0 <= bits)) (PreH15 : (bits <= 65535)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH18 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH19 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> 0)
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSFlagCreate_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (0 = 0)) (PreH2 : (0 = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_effect sg entry bits (LitMap (("?"%string))) 0 114 entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : ((flag_create_free_head (sg) (entry)) = 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : ((flag_create_depth (before)) <= 0)) (PreH11 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flags_pre = bits)) (PreH14 : (0 <= bits)) (PreH15 : (bits <= 65535)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH18 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH19 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (0 = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) 0 114 entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ ((flag_create_free_head (sg) (entry)) = 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_partial_solve_wit_13 := OSFlagCreate_partial_solve_wit_13_pure -> OSFlagCreate_partial_solve_wit_13_aux.

Definition OSFlagCreate_partial_solve_wit_14 := 
forall (perr_pre: Z) (flags_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (literals: (@list string)) (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (error_addr: Z) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (0 = (flag_create_free_head (sg) (entry_2)))) (PreH3 : (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) 0 114 entry_2 )) (PreH4 : (UCOS2_state_inv sg entry_2 )) (PreH5 : ((flag_create_free_head (sg) (entry_2)) = 0)) (PreH6 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH9 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : ((flag_create_depth (before)) <= 0)) (PreH11 : ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0)) (PreH12 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flags_pre = bits)) (PreH14 : (0 <= bits)) (PreH15 : (bits <= 65535)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH18 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH19 : (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 entry_2 )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
|--
  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (0 = (flag_create_free_head (sg) (entry_2))) ” 
  &&  “ (flag_create_effect sg entry_2 bits (LitMap (("?"%string))) 0 114 entry_2 ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ ((flag_create_free_head (sg) (entry_2)) = 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_create_depth (before))) (32)) <= 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flags_pre = bits) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) ) ” 
  &&  “ (flag_create_safe critical sg invocation bits (LitMap (("?"%string))) before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 entry_2 )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (GlobalStrings_missing LitMap literals )
.

Definition OSFlagCreate_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
).

Definition OSFlagCreate_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
.

Definition OSFlagCreate_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (0 < (flag_create_depth (before))) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSFlagCreate_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (0 < (flag_create_depth (before)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSFlagCreate_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : ((flag_create_depth (before)) <= 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
|--
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : ((flag_create_depth (before)) <= 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSFlagCreate_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : ((flag_create_depth (before)) <= 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (flag_create_depth (before)))
  **  (flag_create_interrupt_frame platform critical sg invocation origin mask before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSFlagCreate_which_implies_wit_4 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_create_free_head (sg) (entry)))
  **  (flag_create_pool_frame sg entry )
).

Definition OSFlagCreate_which_implies_wit_5 := 
(
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (bits: Z) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pgrp: Z) (cpu_sr: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : ((flag_create_depth (before)) <= 0)) (PreH7 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH8 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  (flag_create_pool_frame sg entry )
|--
  EX (rest: (@list Z))  (old: FlagGroupImage)  (id: Z) ,
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (pgrp = (flag_pool_addr (sg) (id))) ” 
  &&  “ (pgrp = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (pgrp <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ”
  &&  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (flag_create_fields_frame sg entry id old )
) \/
(
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (bits: Z) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (pgrp: Z) (cpu_sr: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : ((flag_create_depth (before)) <= 0)) (PreH7 : (flag_create_name_admission critical sg invocation before (LitMap (("?"%string))) )) (PreH8 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) ,
  (flag_create_pool_frame sg entry )
|--
  EX (rest: (@list Z))  (old: FlagGroupImage)  (id: Z) ,
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (pgrp = (flag_pool_addr (sg) (id))) ” 
  &&  “ (pgrp = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (pgrp <> 0) ” 
  &&  “ (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ ((flag_create_depth (before)) <= 0) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_create_slot sg entry id rest old ) ” 
  &&  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ”
  &&  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (old)))
  **  (flag_create_fields_frame sg entry id old )
).

Definition OSFlagCreate_which_implies_wit_6 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  (flag_create_fields_frame sg entry id old )
|--
  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ”
  &&  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  (flag_create_fields_frame sg entry id old )
|--
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
).

Definition OSFlagCreate_which_implies_wit_6_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  (flag_create_fields_frame sg entry id old )
|--
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
.

Definition OSFlagCreate_which_implies_wit_7 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
|--
  “ (flag_create_default_name entry (LitMap (("?"%string))) ) ”
  &&  (flag_create_fields_frame sg entry id old )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
|--
  (flag_create_fields_frame sg entry id old )
).

Definition OSFlagCreate_which_implies_wit_7_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (old: FlagGroupImage) (PreH1 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (flag_create_literal_frame sg entry id old (LitMap (("?"%string))) )
|--
  (flag_create_fields_frame sg entry id old )
.

Definition OSFlagCreate_which_implies_wit_8 := 
(
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (pgrp: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_slot sg entry id rest old )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (flag_create_fields_frame sg entry id old )
|--
  “ (pgrp = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (pgrp <> 0) ” 
  &&  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) pgrp 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ”
  &&  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
) \/
(
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (pgrp: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_slot sg entry id rest old )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (flag_create_fields_frame sg entry id old )
|--
  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ” 
  &&  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) pgrp 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ”
  &&  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
).

Definition OSFlagCreate_which_implies_wit_8_split_goal_1 := 
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (pgrp: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_slot sg entry id rest old )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (flag_create_fields_frame sg entry id old )
|--
  “ (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ”
.

Definition OSFlagCreate_which_implies_wit_8_split_goal_2 := 
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (pgrp: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_slot sg entry id rest old )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (flag_create_fields_frame sg entry id old )
|--
  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) pgrp 0 (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) ) ”
.

Definition OSFlagCreate_which_implies_wit_8_split_goal_spatial := 
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (id: Z) (rest: (@list Z)) (old: FlagGroupImage) (pgrp: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) (PreH3 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH4 : (pgrp <> 0)) (PreH5 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH6 : (flag_create_slot sg entry id rest old )) (PreH7 : (flag_create_default_name entry (LitMap (("?"%string))) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flagImageHead (old)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 5)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (flag_create_fields_frame sg entry id old )
|--
  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
.

Definition OSFlagCreate_which_implies_wit_9 := 
(
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
|--
  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
) \/
(
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
).

Definition OSFlagCreate_which_implies_wit_9_split_goal_spatial := 
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (bits: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (UCOS2_state_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry (flag_create_checkpoint (entry) (bits) ((LitMap (("?"%string))))) )
.

Definition OSFlagCreate_which_implies_wit_10 := 
(
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (pgrp: Z) (PreH1 : (pgrp = 0)) (PreH2 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  (flag_create_pool_frame sg entry )
|--
  “ (pgrp = 0) ” 
  &&  “ (pgrp = (flag_create_free_head (sg) (entry))) ” 
  &&  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) pgrp 114 entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  (UCOS2_inv sg entry )
) \/
(
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (pgrp: Z) (PreH1 : (pgrp = 0)) (PreH2 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  (flag_create_pool_frame sg entry )
|--
  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) 0 114 entry ) ”
  &&  (UCOS2_inv sg entry )
).

Definition OSFlagCreate_which_implies_wit_10_split_goal_1 := 
forall (sg: StableGlobVars) (entry: UCOS2_Verify_State) (pgrp: Z) (PreH1 : (pgrp = 0)) (PreH2 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  (flag_create_pool_frame sg entry )
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSFlagCreate_which_implies_wit_10_split_goal_2 := 
forall (LitMap: (string -> Z)) (bits: Z) (sg: StableGlobVars) (entry: UCOS2_Verify_State) (pgrp: Z) (PreH1 : (pgrp = 0)) (PreH2 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  (flag_create_pool_frame sg entry )
|--
  “ (flag_create_effect sg entry bits (LitMap (("?"%string))) 0 114 entry ) ”
.

Definition OSFlagCreate_which_implies_wit_10_split_goal_spatial := 
forall (sg: StableGlobVars) (entry: UCOS2_Verify_State) (pgrp: Z) (PreH1 : (pgrp = 0)) (PreH2 : (pgrp = (flag_create_free_head (sg) (entry)))) (PreH3 : (flag_create_layout sg ( &( "OSIntNesting" ) ) ( &( "OSFlagFreeList" ) ) )) ,
  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pgrp)
  **  (flag_create_pool_frame sg entry )
|--
  (UCOS2_inv sg entry )
.

Definition OSFlagCreate_which_implies_wit_11 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (UCOS2_state_inv sg entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
|--
  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (UCOS2_state_inv sg entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
).

Definition OSFlagCreate_which_implies_wit_11_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (UCOS2_state_inv sg entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry entry )
.

Module Type VC_Correct.


Axiom proof_of_OSFlagCreate_safety_wit_1 : OSFlagCreate_safety_wit_1.
Axiom proof_of_OSFlagCreate_safety_wit_2 : OSFlagCreate_safety_wit_2.
Axiom proof_of_OSFlagCreate_safety_wit_3 : OSFlagCreate_safety_wit_3.
Axiom proof_of_OSFlagCreate_safety_wit_4 : OSFlagCreate_safety_wit_4.
Axiom proof_of_OSFlagCreate_safety_wit_5 : OSFlagCreate_safety_wit_5.
Axiom proof_of_OSFlagCreate_safety_wit_6 : OSFlagCreate_safety_wit_6.
Axiom proof_of_OSFlagCreate_safety_wit_7 : OSFlagCreate_safety_wit_7.
Axiom proof_of_OSFlagCreate_return_wit_1 : OSFlagCreate_return_wit_1.
Axiom proof_of_OSFlagCreate_return_wit_2 : OSFlagCreate_return_wit_2.
Axiom proof_of_OSFlagCreate_return_wit_3 : OSFlagCreate_return_wit_3.
Axiom proof_of_OSFlagCreate_partial_solve_wit_1_pure : OSFlagCreate_partial_solve_wit_1_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_1 : OSFlagCreate_partial_solve_wit_1.
Axiom proof_of_OSFlagCreate_partial_solve_wit_2_pure : OSFlagCreate_partial_solve_wit_2_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_2 : OSFlagCreate_partial_solve_wit_2.
Axiom proof_of_OSFlagCreate_partial_solve_wit_3_pure : OSFlagCreate_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_3 : OSFlagCreate_partial_solve_wit_3.
Axiom proof_of_OSFlagCreate_partial_solve_wit_4 : OSFlagCreate_partial_solve_wit_4.
Axiom proof_of_OSFlagCreate_partial_solve_wit_5_pure : OSFlagCreate_partial_solve_wit_5_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_5 : OSFlagCreate_partial_solve_wit_5.
Axiom proof_of_OSFlagCreate_partial_solve_wit_6_pure : OSFlagCreate_partial_solve_wit_6_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_6 : OSFlagCreate_partial_solve_wit_6.
Axiom proof_of_OSFlagCreate_partial_solve_wit_7_pure : OSFlagCreate_partial_solve_wit_7_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_7 : OSFlagCreate_partial_solve_wit_7.
Axiom proof_of_OSFlagCreate_partial_solve_wit_8_pure : OSFlagCreate_partial_solve_wit_8_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_8 : OSFlagCreate_partial_solve_wit_8.
Axiom proof_of_OSFlagCreate_partial_solve_wit_9_pure : OSFlagCreate_partial_solve_wit_9_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_9 : OSFlagCreate_partial_solve_wit_9.
Axiom proof_of_OSFlagCreate_partial_solve_wit_10_pure : OSFlagCreate_partial_solve_wit_10_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_10 : OSFlagCreate_partial_solve_wit_10.
Axiom proof_of_OSFlagCreate_partial_solve_wit_11 : OSFlagCreate_partial_solve_wit_11.
Axiom proof_of_OSFlagCreate_partial_solve_wit_12_pure : OSFlagCreate_partial_solve_wit_12_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_12 : OSFlagCreate_partial_solve_wit_12.
Axiom proof_of_OSFlagCreate_partial_solve_wit_13_pure : OSFlagCreate_partial_solve_wit_13_pure.
Axiom proof_of_OSFlagCreate_partial_solve_wit_13 : OSFlagCreate_partial_solve_wit_13.
Axiom proof_of_OSFlagCreate_partial_solve_wit_14 : OSFlagCreate_partial_solve_wit_14.
Axiom proof_of_OSFlagCreate_which_implies_wit_1 : OSFlagCreate_which_implies_wit_1.
Axiom proof_of_OSFlagCreate_which_implies_wit_2 : OSFlagCreate_which_implies_wit_2.
Axiom proof_of_OSFlagCreate_which_implies_wit_3 : OSFlagCreate_which_implies_wit_3.
Axiom proof_of_OSFlagCreate_which_implies_wit_4 : OSFlagCreate_which_implies_wit_4.
Axiom proof_of_OSFlagCreate_which_implies_wit_5 : OSFlagCreate_which_implies_wit_5.
Axiom proof_of_OSFlagCreate_which_implies_wit_6 : OSFlagCreate_which_implies_wit_6.
Axiom proof_of_OSFlagCreate_which_implies_wit_7 : OSFlagCreate_which_implies_wit_7.
Axiom proof_of_OSFlagCreate_which_implies_wit_8 : OSFlagCreate_which_implies_wit_8.
Axiom proof_of_OSFlagCreate_which_implies_wit_9 : OSFlagCreate_which_implies_wit_9.
Axiom proof_of_OSFlagCreate_which_implies_wit_10 : OSFlagCreate_which_implies_wit_10.
Axiom proof_of_OSFlagCreate_which_implies_wit_11 : OSFlagCreate_which_implies_wit_11.

End VC_Correct.
