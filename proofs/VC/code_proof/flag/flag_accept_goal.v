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
Require Import Ucos2Verify.VC.code.flag.spec.flag_accept_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSFlagAccept -----*)

Definition OSFlagAccept_safety_wit_1 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = pe)) (PreH2 : (perr_pre = error_addr)) (PreH3 : (flags_pre = requested)) (PreH4 : (wait_type_pre = wait_request)) (PreH5 : (flag_accept_profile sg )) (PreH6 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_2 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flags_pre = requested)) (PreH5 : (wait_type_pre = wait_request)) (PreH6 : (flag_accept_profile sg )) (PreH7 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 110)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_3 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_4 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= wait_type_pre)) (PreH2 : (wait_type_pre <= 255)) (PreH3 : (0 <= flags_pre)) (PreH4 : (flags_pre <= 65535)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_accept_profile sg )) (PreH8 : ((flagImageType (observed)) = 5)) (PreH9 : (flag_accept_admission sg pe view before observed )) (PreH10 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH11 : (flag_accept_profile sg )) (PreH12 : (pe <> 0)) (PreH13 : (pgrp_pre <> 0)) (PreH14 : (pgrp_pre = pe)) (PreH15 : (perr_pre = error_addr)) (PreH16 : (flags_pre = requested)) (PreH17 : (wait_type_pre = wait_request)) (PreH18 : (flag_accept_profile sg )) (PreH19 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |-> (Z.land wait_type_pre 128))
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_5 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "wait_type" ) )) # UChar  |-> (Z.land wait_type_pre (Z.lnot 128)))
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "consume" ) )) # UChar  |-> 1)
  **  ((( &( "result" ) )) # UChar  |-> (Z.land wait_type_pre 128))
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_6 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "consume" ) )) # UChar  |-> 0)
  **  ((( &( "result" ) )) # UChar  |-> (Z.land wait_type_pre 128))
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_7 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_8 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 = wait_type)) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> acquired_saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |-> (Z.land (flagImageBits (image)) requested))
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_9 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_10 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_11 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 <> wait_type)) (PreH11 : (0 <> wait_type)) (PreH12 : (1 = wait_type)) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> acquired_saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |-> (Z.land (Z.lnot (flagImageBits (image))) requested))
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_12 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_13 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((error_addr) # UChar  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_safety_wit_14 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((error_addr) # UChar  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagAccept_entail_wit_1 := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : ((flagImageType (observed)) = 5)) (PreH3 : (flag_accept_admission sg pe view before observed )) (PreH4 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH5 : (flag_accept_profile sg )) (PreH6 : (pe <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (pgrp_pre = pe)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (flags_pre = requested)) (PreH11 : (wait_type_pre = wait_request)) (PreH12 : (flag_accept_profile sg )) (PreH13 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= wait_type_pre) ” 
  &&  “ (wait_type_pre <= 255) ” 
  &&  “ (0 <= flags_pre) ” 
  &&  “ (flags_pre <= 65535) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_accept_profile sg )) (PreH4 : ((flagImageType (observed)) = 5)) (PreH5 : (flag_accept_admission sg pe view before observed )) (PreH6 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH7 : (flag_accept_profile sg )) (PreH8 : (pe <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = pe)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flags_pre = requested)) (PreH13 : (wait_type_pre = wait_request)) (PreH14 : (flag_accept_profile sg )) (PreH15 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  TT && emp 
|--
  “ (flags_pre <= 65535) ” 
  &&  “ (0 <= flags_pre) ” 
  &&  “ (wait_type_pre <= 255) ” 
  &&  “ (0 <= wait_type_pre) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_accept_profile sg )) (PreH4 : ((flagImageType (observed)) = 5)) (PreH5 : (flag_accept_admission sg pe view before observed )) (PreH6 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH7 : (flag_accept_profile sg )) (PreH8 : (pe <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = pe)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flags_pre = requested)) (PreH13 : (wait_type_pre = wait_request)) (PreH14 : (flag_accept_profile sg )) (PreH15 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (flags_pre <= 65535)
.

Definition OSFlagAccept_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_accept_profile sg )) (PreH4 : ((flagImageType (observed)) = 5)) (PreH5 : (flag_accept_admission sg pe view before observed )) (PreH6 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH7 : (flag_accept_profile sg )) (PreH8 : (pe <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = pe)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flags_pre = requested)) (PreH13 : (wait_type_pre = wait_request)) (PreH14 : (flag_accept_profile sg )) (PreH15 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (0 <= flags_pre)
.

Definition OSFlagAccept_entail_wit_1_split_goal_3 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_accept_profile sg )) (PreH4 : ((flagImageType (observed)) = 5)) (PreH5 : (flag_accept_admission sg pe view before observed )) (PreH6 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH7 : (flag_accept_profile sg )) (PreH8 : (pe <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = pe)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flags_pre = requested)) (PreH13 : (wait_type_pre = wait_request)) (PreH14 : (flag_accept_profile sg )) (PreH15 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (wait_type_pre <= 255)
.

Definition OSFlagAccept_entail_wit_1_split_goal_4 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_accept_profile sg )) (PreH4 : ((flagImageType (observed)) = 5)) (PreH5 : (flag_accept_admission sg pe view before observed )) (PreH6 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH7 : (flag_accept_profile sg )) (PreH8 : (pe <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (pgrp_pre = pe)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (flags_pre = requested)) (PreH13 : (wait_type_pre = wait_request)) (PreH14 : (flag_accept_profile sg )) (PreH15 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (0 <= wait_type_pre)
.

Definition OSFlagAccept_entail_wit_2_1 := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask retval view pe before observed entry image )
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ ((Z.land wait_type_pre (Z.lnot 128)) = (flag_accept_mode (wait_request))) ” 
  &&  “ ((Z.land wait_type_pre 128) = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (1 = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask retval view pe before observed entry image )
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  TT && emp 
|--
  “ (1 = (flag_accept_consume_value (wait_type_pre))) ” 
  &&  “ ((Z.land wait_type_pre 128) = (flag_accept_consume_bit (wait_type_pre))) ” 
  &&  “ ((Z.land wait_type_pre (Z.lnot 128)) = (flag_accept_mode (wait_type_pre))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_2_1_split_goal_1 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (1 = (flag_accept_consume_value (wait_type_pre)))
.

Definition OSFlagAccept_entail_wit_2_1_split_goal_2 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((Z.land wait_type_pre 128) = (flag_accept_consume_bit (wait_type_pre)))
.

Definition OSFlagAccept_entail_wit_2_1_split_goal_3 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((Z.land wait_type_pre (Z.lnot 128)) = (flag_accept_mode (wait_type_pre)))
.

Definition OSFlagAccept_entail_wit_2_2 := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask retval view pe before observed entry image )
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type_pre = (flag_accept_mode (wait_request))) ” 
  &&  “ ((Z.land wait_type_pre 128) = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (0 = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask retval view pe before observed entry image )
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  TT && emp 
|--
  “ (0 = (flag_accept_consume_value (wait_type_pre))) ” 
  &&  “ ((Z.land wait_type_pre 128) = (flag_accept_consume_bit (wait_type_pre))) ” 
  &&  “ (wait_type_pre = (flag_accept_mode (wait_type_pre))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_2_2_split_goal_1 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (0 = (flag_accept_consume_value (wait_type_pre)))
.

Definition OSFlagAccept_entail_wit_2_2_split_goal_2 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((Z.land wait_type_pre 128) = (flag_accept_consume_bit (wait_type_pre)))
.

Definition OSFlagAccept_entail_wit_2_2_split_goal_3 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry_2 )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (wait_type_pre = (flag_accept_mode (wait_type_pre)))
.

Definition OSFlagAccept_entail_wit_3_1 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (flagImageBits (image)) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) (Z.land (flagImageBits (image)) requested) 0 ) ” 
  &&  “ ((Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) <= 65535) ” 
  &&  “ (0 <= (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16)))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_3_1_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) (Z.land (flagImageBits (image)) requested) 0 )
.

Definition OSFlagAccept_entail_wit_3_1_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  ((Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) <= 65535)
.

Definition OSFlagAccept_entail_wit_3_1_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  (0 <= (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))))
.

Definition OSFlagAccept_entail_wit_3_2 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (flagImageBits (image)) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (flagImageBits (image)) requested) 0 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_3_2_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (flagImageBits (image)) requested) 0 )
.

Definition OSFlagAccept_entail_wit_3_2_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_3_2_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_3_3 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 112)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (flagImageBits (image)) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (flagImageBits (image)) requested) 112 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_3_3_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (flagImageBits (image)) requested) 112 )
.

Definition OSFlagAccept_entail_wit_3_3_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_3_3_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_4_1 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (flagImageBits (image)) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) (Z.land (flagImageBits (image)) requested) 0 ) ” 
  &&  “ ((Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) <= 65535) ” 
  &&  “ (0 <= (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16)))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_4_1_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) (Z.land (flagImageBits (image)) requested) 0 )
.

Definition OSFlagAccept_entail_wit_4_1_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  ((Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))) <= 65535)
.

Definition OSFlagAccept_entail_wit_4_1_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  (0 <= (Z.land (flagImageBits (image)) (unsigned_last_nbits ((Z.lnot (Z.land (flagImageBits (image)) requested))) (16))))
.

Definition OSFlagAccept_entail_wit_4_2 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (flagImageBits (image)) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (flagImageBits (image)) requested) 0 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_4_2_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (flagImageBits (image)) requested) 0 )
.

Definition OSFlagAccept_entail_wit_4_2_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_4_2_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (flagImageBits (image)) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_4_3 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 112)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (flagImageBits (image)) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 112 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_4_3_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 112 )
.

Definition OSFlagAccept_entail_wit_4_3_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_4_3_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (flagImageBits (image)) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_5_1 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (Z.lnot (flagImageBits (image))) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 ) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) <= 65535) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_5_1_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 )
.

Definition OSFlagAccept_entail_wit_5_1_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  ((Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) <= 65535)
.

Definition OSFlagAccept_entail_wit_5_1_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)))
.

Definition OSFlagAccept_entail_wit_5_2 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (Z.lnot (flagImageBits (image))) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_5_2_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 )
.

Definition OSFlagAccept_entail_wit_5_2_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_5_2_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = requested)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_5_3 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 112)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (Z.lnot (flagImageBits (image))) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (Z.lnot (flagImageBits (image))) requested) 112 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_5_3_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (Z.lnot (flagImageBits (image))) requested) 112 )
.

Definition OSFlagAccept_entail_wit_5_3_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_5_3_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> requested)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_6_1 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (Z.lnot (flagImageBits (image))) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 ) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) <= 65535) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_6_1_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 )
.

Definition OSFlagAccept_entail_wit_6_1_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  ((Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)) <= 65535)
.

Definition OSFlagAccept_entail_wit_6_1_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) = 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((flagImageBits (image))) (16)) (Z.land (Z.lnot (flagImageBits (image))) requested)))
.

Definition OSFlagAccept_entail_wit_6_2 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (Z.lnot (flagImageBits (image))) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_6_2_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) (Z.land (Z.lnot (flagImageBits (image))) requested) 0 )
.

Definition OSFlagAccept_entail_wit_6_2_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_6_2_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((unsigned_last_nbits (consume) (32)) <> 1)) (PreH2 : ((Z.land (Z.lnot (flagImageBits (image))) requested) <> 0)) (PreH3 : (0 <= wait_request)) (PreH4 : (wait_request <= 255)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (wait_type = (flag_accept_mode (wait_request)))) (PreH8 : (result = (flag_accept_consume_bit (wait_request)))) (PreH9 : (consume = (flag_accept_consume_value (wait_request)))) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (2 <> wait_type)) (PreH12 : (3 <> wait_type)) (PreH13 : (0 <> wait_type)) (PreH14 : (1 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_6_3 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 <> wait_type)) (PreH13 : (1 = wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 112)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  EX (error: Z)  (bits: Z) ,
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request bits (Z.land (Z.lnot (flagImageBits (image))) requested) error ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 <> wait_type)) (PreH13 : (1 = wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 112 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_6_3_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 <> wait_type)) (PreH13 : (1 = wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 112 )
.

Definition OSFlagAccept_entail_wit_6_3_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 <> wait_type)) (PreH13 : (1 = wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_6_3_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : ((Z.land (Z.lnot (flagImageBits (image))) requested) = 0)) (PreH2 : (0 <= wait_request)) (PreH3 : (wait_request <= 255)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (wait_type = (flag_accept_mode (wait_request)))) (PreH7 : (result = (flag_accept_consume_bit (wait_request)))) (PreH8 : (consume = (flag_accept_consume_value (wait_request)))) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH10 : (2 <> wait_type)) (PreH11 : (3 <> wait_type)) (PreH12 : (0 <> wait_type)) (PreH13 : (1 = wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_entail_wit_7 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 <> wait_type)) (PreH11 : (0 <> wait_type)) (PreH12 : (1 <> wait_type)) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
|--
  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= (flagImageBits (image))) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ”
  &&  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask acquired_saved view pe before observed entry image )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 <> wait_type)) (PreH11 : (0 <> wait_type)) (PreH12 : (1 <> wait_type)) ,
  TT && emp 
|--
  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= (flagImageBits (image))) ”
  &&  emp
).

Definition OSFlagAccept_entail_wit_7_split_goal_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (acquired_saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 <> wait_type)) (PreH11 : (0 <> wait_type)) (PreH12 : (1 <> wait_type)) ,
  (flag_accept_checkpoint_facts critical sg invocation irq_mask acquired_saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )
.

Definition OSFlagAccept_entail_wit_7_split_goal_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 <> wait_type)) (PreH11 : (0 <> wait_type)) (PreH12 : (1 <> wait_type)) ,
  ((flagImageBits (image)) <= 65535)
.

Definition OSFlagAccept_entail_wit_7_split_goal_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH9 : (2 <> wait_type)) (PreH10 : (3 <> wait_type)) (PreH11 : (0 <> wait_type)) (PreH12 : (1 <> wait_type)) ,
  (0 <= (flagImageBits (image)))
.

Definition OSFlagAccept_return_wit_1 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
.

Definition OSFlagAccept_return_wit_2 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
.

Definition OSFlagAccept_return_wit_3 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
.

Definition OSFlagAccept_return_wit_4 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
  **  (caller_frame )
.

Definition OSFlagAccept_return_wit_5 := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
.

Definition OSFlagAccept_return_wit_6 := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
).

Definition OSFlagAccept_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |-> 1)
  **  (caller_frame )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
.

Definition OSFlagAccept_return_wit_7 := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flags_pre = requested)) (PreH5 : (wait_type_pre = wait_request)) (PreH6 : (flag_accept_profile sg )) (PreH7 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((perr_pre) # UChar  |-> 110)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flags_pre = requested)) (PreH5 : (wait_type_pre = wait_request)) (PreH6 : (flag_accept_profile sg )) (PreH7 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((perr_pre) # UChar  |-> 110)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
).

Definition OSFlagAccept_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (pgrp_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flags_pre = requested)) (PreH5 : (wait_type_pre = wait_request)) (PreH6 : (flag_accept_profile sg )) (PreH7 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((perr_pre) # UChar  |-> 110)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flags_pre = requested)) (PreH5 : (wait_type_pre = wait_request)) (PreH6 : (flag_accept_profile sg )) (PreH7 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ”
.

Definition OSFlagAccept_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (pgrp_pre = pe)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (flags_pre = requested)) (PreH5 : (wait_type_pre = wait_request)) (PreH6 : (flag_accept_profile sg )) (PreH7 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
  **  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_1 := OSFlagAccept_partial_solve_wit_1_pure -> OSFlagAccept_partial_solve_wit_1_aux.

Definition OSFlagAccept_partial_solve_wit_2 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) (PreH3 : (pgrp_pre <> 0)) (PreH4 : (pgrp_pre = pe)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (flags_pre = requested)) (PreH7 : (wait_type_pre = wait_request)) (PreH8 : (flag_accept_profile sg )) (PreH9 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((flagImageType (observed)) <> 5) ”
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH4 : (flag_accept_profile sg )) (PreH5 : (pe <> 0)) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = pe)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flags_pre = requested)) (PreH10 : (wait_type_pre = wait_request)) (PreH11 : (flag_accept_profile sg )) (PreH12 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) <> 5) ”
).

Definition OSFlagAccept_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH4 : (flag_accept_profile sg )) (PreH5 : (pe <> 0)) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = pe)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flags_pre = requested)) (PreH10 : (wait_type_pre = wait_request)) (PreH11 : (flag_accept_profile sg )) (PreH12 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) <> 5) ”
.

Definition OSFlagAccept_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((flagImageType (observed)) <> 5) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_3 := OSFlagAccept_partial_solve_wit_3_pure -> OSFlagAccept_partial_solve_wit_3_aux.

Definition OSFlagAccept_partial_solve_wit_4_pure := 
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ”
) \/
(
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH4 : (flag_accept_profile sg )) (PreH5 : (pe <> 0)) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = pe)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flags_pre = requested)) (PreH10 : (wait_type_pre = wait_request)) (PreH11 : (flag_accept_profile sg )) (PreH12 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) = 5) ”
).

Definition OSFlagAccept_partial_solve_wit_4_pure_split_goal_1 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH4 : (flag_accept_profile sg )) (PreH5 : (pe <> 0)) (PreH6 : (pgrp_pre <> 0)) (PreH7 : (pgrp_pre = pe)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (flags_pre = requested)) (PreH10 : (wait_type_pre = wait_request)) (PreH11 : (flag_accept_profile sg )) (PreH12 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "consume" ) )) # UChar  |->_)
  **  ((( &( "result" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ ((flagImageType (observed)) = 5) ”
.

Definition OSFlagAccept_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (flag_accept_profile sg )) (PreH3 : (pe <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (pgrp_pre = pe)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (flags_pre = requested)) (PreH8 : (wait_type_pre = wait_request)) (PreH9 : (flag_accept_profile sg )) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
  **  ((perr_pre) # UChar  |->_)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_4 := OSFlagAccept_partial_solve_wit_4_pure -> OSFlagAccept_partial_solve_wit_4_aux.

Definition OSFlagAccept_partial_solve_wit_5 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land wait_type_pre 128) <> 0)) (PreH2 : (0 <= wait_type_pre)) (PreH3 : (wait_type_pre <= 255)) (PreH4 : (0 <= flags_pre)) (PreH5 : (flags_pre <= 65535)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (flag_accept_profile sg )) (PreH9 : ((flagImageType (observed)) = 5)) (PreH10 : (flag_accept_admission sg pe view before observed )) (PreH11 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH12 : (flag_accept_profile sg )) (PreH13 : (pe <> 0)) (PreH14 : (pgrp_pre <> 0)) (PreH15 : (pgrp_pre = pe)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (flags_pre = requested)) (PreH18 : (wait_type_pre = wait_request)) (PreH19 : (flag_accept_profile sg )) (PreH20 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ ((Z.land wait_type_pre 128) <> 0) ” 
  &&  “ (0 <= wait_type_pre) ” 
  &&  “ (wait_type_pre <= 255) ” 
  &&  “ (0 <= flags_pre) ” 
  &&  “ (flags_pre <= 65535) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_6 := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((Z.land wait_type_pre 128) = 0)) (PreH2 : (0 <= wait_type_pre)) (PreH3 : (wait_type_pre <= 255)) (PreH4 : (0 <= flags_pre)) (PreH5 : (flags_pre <= 65535)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (flag_accept_profile sg )) (PreH9 : ((flagImageType (observed)) = 5)) (PreH10 : (flag_accept_admission sg pe view before observed )) (PreH11 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH12 : (flag_accept_profile sg )) (PreH13 : (pe <> 0)) (PreH14 : (pgrp_pre <> 0)) (PreH15 : (pgrp_pre = pe)) (PreH16 : (perr_pre = error_addr)) (PreH17 : (flags_pre = requested)) (PreH18 : (wait_type_pre = wait_request)) (PreH19 : (flag_accept_profile sg )) (PreH20 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ ((Z.land wait_type_pre 128) = 0) ” 
  &&  “ (0 <= wait_type_pre) ” 
  &&  “ (wait_type_pre <= 255) ” 
  &&  “ (0 <= flags_pre) ” 
  &&  “ (flags_pre <= 65535) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "consume" ) )) # UChar  |-> 0)
  **  ((( &( "result" ) )) # UChar  |-> (Z.land wait_type_pre 128))
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation irq_mask retval before entry ) ”
.

Definition OSFlagAccept_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry )) (PreH2 : ((Z.land wait_type_pre 128) = 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation irq_mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation irq_mask retval before entry ) ” 
  &&  “ ((Z.land wait_type_pre 128) = 0) ” 
  &&  “ (0 <= wait_type_pre) ” 
  &&  “ (wait_type_pre <= 255) ” 
  &&  “ (0 <= flags_pre) ” 
  &&  “ (flags_pre <= 65535) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_7 := OSFlagAccept_partial_solve_wit_7_pure -> OSFlagAccept_partial_solve_wit_7_aux.

Definition OSFlagAccept_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "wait_type" ) )) # UChar  |-> (Z.land wait_type_pre (Z.lnot 128)))
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  (flag_accept_source_rep sg pe view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "consume" ) )) # UChar  |-> 1)
  **  ((( &( "result" ) )) # UChar  |-> (Z.land wait_type_pre 128))
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation irq_mask retval before entry ) ”
.

Definition OSFlagAccept_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pgrp_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation irq_mask retval before entry )) (PreH2 : ((Z.land wait_type_pre 128) <> 0)) (PreH3 : (0 <= wait_type_pre)) (PreH4 : (wait_type_pre <= 255)) (PreH5 : (0 <= flags_pre)) (PreH6 : (flags_pre <= 65535)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (flag_accept_profile sg )) (PreH10 : ((flagImageType (observed)) = 5)) (PreH11 : (flag_accept_admission sg pe view before observed )) (PreH12 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH13 : (flag_accept_profile sg )) (PreH14 : (pe <> 0)) (PreH15 : (pgrp_pre <> 0)) (PreH16 : (pgrp_pre = pe)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (flags_pre = requested)) (PreH19 : (wait_type_pre = wait_request)) (PreH20 : (flag_accept_profile sg )) (PreH21 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation irq_mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation irq_mask retval before entry ) ” 
  &&  “ ((Z.land wait_type_pre 128) <> 0) ” 
  &&  “ (0 <= wait_type_pre) ” 
  &&  “ (wait_type_pre <= 255) ” 
  &&  “ (0 <= flags_pre) ” 
  &&  “ (flags_pre <= 65535) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ” 
  &&  “ ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (pgrp_pre = pe) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (flags_pre = requested) ” 
  &&  “ (wait_type_pre = wait_request) ” 
  &&  “ (flag_accept_profile sg ) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (flag_accept_source_rep sg pe view )
  **  ((perr_pre) # UChar  |-> 0)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_8 := OSFlagAccept_partial_solve_wit_8_pure -> OSFlagAccept_partial_solve_wit_8_aux.

Definition OSFlagAccept_partial_solve_wit_9_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ”
.

Definition OSFlagAccept_partial_solve_wit_9_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_9 := OSFlagAccept_partial_solve_wit_9_pure -> OSFlagAccept_partial_solve_wit_9_aux.

Definition OSFlagAccept_partial_solve_wit_10_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ”
.

Definition OSFlagAccept_partial_solve_wit_10_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_10 := OSFlagAccept_partial_solve_wit_10_pure -> OSFlagAccept_partial_solve_wit_10_aux.

Definition OSFlagAccept_partial_solve_wit_11_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
.

Definition OSFlagAccept_partial_solve_wit_11_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_11 := OSFlagAccept_partial_solve_wit_11_pure -> OSFlagAccept_partial_solve_wit_11_aux.

Definition OSFlagAccept_partial_solve_wit_12_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ”
.

Definition OSFlagAccept_partial_solve_wit_12_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_12 := OSFlagAccept_partial_solve_wit_12_pure -> OSFlagAccept_partial_solve_wit_12_aux.

Definition OSFlagAccept_partial_solve_wit_13_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ”
.

Definition OSFlagAccept_partial_solve_wit_13_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_13 := OSFlagAccept_partial_solve_wit_13_pure -> OSFlagAccept_partial_solve_wit_13_aux.

Definition OSFlagAccept_partial_solve_wit_14_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
.

Definition OSFlagAccept_partial_solve_wit_14_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_14 := OSFlagAccept_partial_solve_wit_14_pure -> OSFlagAccept_partial_solve_wit_14_aux.

Definition OSFlagAccept_partial_solve_wit_15_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ”
.

Definition OSFlagAccept_partial_solve_wit_15_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_15 := OSFlagAccept_partial_solve_wit_15_pure -> OSFlagAccept_partial_solve_wit_15_aux.

Definition OSFlagAccept_partial_solve_wit_16_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ”
.

Definition OSFlagAccept_partial_solve_wit_16_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_16 := OSFlagAccept_partial_solve_wit_16_pure -> OSFlagAccept_partial_solve_wit_16_aux.

Definition OSFlagAccept_partial_solve_wit_17_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
.

Definition OSFlagAccept_partial_solve_wit_17_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_17 := OSFlagAccept_partial_solve_wit_17_pure -> OSFlagAccept_partial_solve_wit_17_aux.

Definition OSFlagAccept_partial_solve_wit_18_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ”
.

Definition OSFlagAccept_partial_solve_wit_18_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_18 := OSFlagAccept_partial_solve_wit_18_pure -> OSFlagAccept_partial_solve_wit_18_aux.

Definition OSFlagAccept_partial_solve_wit_19_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ”
.

Definition OSFlagAccept_partial_solve_wit_19_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (saved = saved) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
.

Definition OSFlagAccept_partial_solve_wit_19 := OSFlagAccept_partial_solve_wit_19_pure -> OSFlagAccept_partial_solve_wit_19_aux.

Definition OSFlagAccept_partial_solve_wit_20_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> ready)
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
.

Definition OSFlagAccept_partial_solve_wit_20_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= bits)) (PreH9 : (bits <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> error)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error ) ”
  &&  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_20 := OSFlagAccept_partial_solve_wit_20_pure -> OSFlagAccept_partial_solve_wit_20_aux.

Definition OSFlagAccept_partial_solve_wit_21_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |-> 0)
  **  ((error_addr) # UChar  |-> 111)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ”
.

Definition OSFlagAccept_partial_solve_wit_21_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> 111)
|--
  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= (flagImageBits (image))) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ”
  &&  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((error_addr) # UChar  |-> 111)
  **  (caller_frame )
.

Definition OSFlagAccept_partial_solve_wit_21 := OSFlagAccept_partial_solve_wit_21_pure -> OSFlagAccept_partial_solve_wit_21_aux.

Definition OSFlagAccept_partial_solve_wit_22_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((error_addr) # UChar  |-> 0)
|--
  “ (saved = saved) ”
.

Definition OSFlagAccept_partial_solve_wit_22_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
|--
  “ (saved = saved) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= (flagImageBits (image))) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
.

Definition OSFlagAccept_partial_solve_wit_22 := OSFlagAccept_partial_solve_wit_22_pure -> OSFlagAccept_partial_solve_wit_22_aux.

Definition OSFlagAccept_partial_solve_wit_23_pure := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "flags" ) )) # UShort  |-> requested)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type)
  **  ((( &( "result" ) )) # UChar  |-> result)
  **  ((( &( "consume" ) )) # UChar  |-> consume)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
  **  (caller_frame )
  **  ((( &( "flags_rdy" ) )) # UShort  |->_)
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= (flagImageBits (image))) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ”
.

Definition OSFlagAccept_partial_solve_wit_23_aux := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (wait_type: Z) (result: Z) (consume: Z) (saved: Z) (PreH1 : (0 <= wait_request)) (PreH2 : (wait_request <= 255)) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (wait_type = (flag_accept_mode (wait_request)))) (PreH6 : (result = (flag_accept_consume_bit (wait_request)))) (PreH7 : (consume = (flag_accept_consume_value (wait_request)))) (PreH8 : (0 <= (flagImageBits (image)))) (PreH9 : ((flagImageBits (image)) <= 65535)) (PreH10 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH11 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
  **  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  “ (0 <= (flagImageBits (image))) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (0 <= wait_request) ” 
  &&  “ (wait_request <= 255) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (wait_type = (flag_accept_mode (wait_request))) ” 
  &&  “ (result = (flag_accept_consume_bit (wait_request))) ” 
  &&  “ (consume = (flag_accept_consume_value (wait_request))) ” 
  &&  “ (0 <= (flagImageBits (image))) ” 
  &&  “ ((flagImageBits (image)) <= 65535) ” 
  &&  “ (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X ) ” 
  &&  “ (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 ) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
  **  (caller_frame )
  **  ((error_addr) # UChar  |-> 0)
.

Definition OSFlagAccept_partial_solve_wit_23 := OSFlagAccept_partial_solve_wit_23_pure -> OSFlagAccept_partial_solve_wit_23_aux.

Definition OSFlagAccept_which_implies_wit_1 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ (pe <> 0) ”
  &&  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
).

Definition OSFlagAccept_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) ,
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
|--
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
.

Definition OSFlagAccept_which_implies_wit_2 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) (PreH3 : ((flagImageType (observed)) <> 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) (PreH3 : ((flagImageType (observed)) <> 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
).

Definition OSFlagAccept_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) (PreH3 : ((flagImageType (observed)) <> 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  (flag_accept_before_resource platform critical sg invocation origin irq_mask view pe before observed )
.

Definition OSFlagAccept_which_implies_wit_3 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : ((flagImageType (observed)) = 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  “ (flag_accept_profile sg ) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_accept_admission sg pe view before observed ) ”
  &&  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : ((flagImageType (observed)) = 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  “ (flag_accept_admission sg pe view before observed ) ”
  &&  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
).

Definition OSFlagAccept_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : ((flagImageType (observed)) = 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  “ (flag_accept_admission sg pe view before observed ) ”
.

Definition OSFlagAccept_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_accept_profile sg )) (PreH2 : ((flagImageType (observed)) = 5)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_accept_type_frame platform sg invocation origin irq_mask view pe before observed )
|--
  (mutex_query_closed platform critical sg invocation origin irq_mask before )
  **  (flag_accept_source_rep sg pe view )
.

Definition OSFlagAccept_which_implies_wit_4 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) (PreH3 : ((flagImageType (observed)) = 5)) (PreH4 : (flag_accept_admission sg pe view before observed )) (PreH5 : (time_get_acquire_facts critical sg invocation irq_mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (flag_accept_source_rep sg pe view )
|--
  EX (entry: UCOS2_Verify_State)  (image: FlagGroupImage) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask cpu_sr view pe before observed entry image )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_accept_profile sg )) (PreH2 : (pe <> 0)) (PreH3 : ((flagImageType (observed)) = 5)) (PreH4 : (flag_accept_admission sg pe view before observed )) (PreH5 : (time_get_acquire_facts critical sg invocation irq_mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (flag_accept_source_rep sg pe view )
|--
  EX (entry: UCOS2_Verify_State)  (image: FlagGroupImage) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask cpu_sr view pe before observed entry image )
).

Definition OSFlagAccept_which_implies_wit_5 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
).

Definition OSFlagAccept_which_implies_wit_5_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
.

Definition OSFlagAccept_which_implies_wit_6 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
).

Definition OSFlagAccept_which_implies_wit_6_split_goal_spatial := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
.

Definition OSFlagAccept_which_implies_wit_7 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
).

Definition OSFlagAccept_which_implies_wit_7_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
.

Definition OSFlagAccept_which_implies_wit_8 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
).

Definition OSFlagAccept_which_implies_wit_8_split_goal_spatial := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
.

Definition OSFlagAccept_which_implies_wit_9 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
).

Definition OSFlagAccept_which_implies_wit_9_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
.

Definition OSFlagAccept_which_implies_wit_10 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
).

Definition OSFlagAccept_which_implies_wit_10_split_goal_spatial := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
.

Definition OSFlagAccept_which_implies_wit_11 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
).

Definition OSFlagAccept_which_implies_wit_11_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (saved: Z) (PreH1 : (0 <= bits)) (PreH2 : (bits <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> bits)
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
.

Definition OSFlagAccept_which_implies_wit_12 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
).

Definition OSFlagAccept_which_implies_wit_12_split_goal_spatial := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (bits: Z) (error: Z) (ready: Z) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request bits ready error )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) (bits)) )
  **  (flag_accept_raw_post sg pe view image bits )
  **  ((error_addr) # UChar  |-> error)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request ready X )
.

Definition OSFlagAccept_which_implies_wit_13 := 
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((error_addr) # UChar  |-> 111)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((error_addr) # UChar  |-> 111)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
).

Definition OSFlagAccept_which_implies_wit_13_split_goal_spatial := 
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (wait_request: Z) (requested: Z) (error_addr: Z) (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (saved: Z) (PreH1 : (flag_accept_safe critical sg invocation view pe (flagImageType (observed)) requested wait_request before X )) (PreH2 : (flag_accept_checkpoint_facts critical sg invocation irq_mask saved view pe before observed entry image requested wait_request (flagImageBits (image)) 0 111 )) ,
  (time_get_restore_post platform critical sg invocation origin saved (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
  **  ((error_addr) # UChar  |-> 111)
|--
  (flag_accept_api_post platform critical sg invocation origin irq_mask view pe error_addr before observed requested wait_request 0 X )
.

Definition OSFlagAccept_which_implies_wit_14 := 
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (saved: Z) (PreH1 : (0 <= (flagImageBits (image)))) (PreH2 : ((flagImageBits (image)) <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
) \/
(
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (saved: Z) (PreH1 : (0 <= (flagImageBits (image)))) (PreH2 : ((flagImageBits (image)) <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
).

Definition OSFlagAccept_which_implies_wit_14_split_goal_spatial := 
forall (pe: Z) (observed: FlagGroupImage) (view: FlagAcceptView) (before: UCOS2_Verify_State) (irq_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (image: FlagGroupImage) (saved: Z) (PreH1 : (0 <= (flagImageBits (image)))) (PreH2 : ((flagImageBits (image)) <= 65535)) ,
  ((&((pe)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  (flag_accept_bits_frame platform critical sg invocation origin irq_mask saved view pe before observed entry image )
|--
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin irq_mask saved entry (flag_accept_released (view) (entry) (image) ((flagImageBits (image)))) )
  **  (flag_accept_raw_post sg pe view image (flagImageBits (image)) )
.

Module Type VC_Correct.


Axiom proof_of_OSFlagAccept_safety_wit_1 : OSFlagAccept_safety_wit_1.
Axiom proof_of_OSFlagAccept_safety_wit_2 : OSFlagAccept_safety_wit_2.
Axiom proof_of_OSFlagAccept_safety_wit_3 : OSFlagAccept_safety_wit_3.
Axiom proof_of_OSFlagAccept_safety_wit_4 : OSFlagAccept_safety_wit_4.
Axiom proof_of_OSFlagAccept_safety_wit_5 : OSFlagAccept_safety_wit_5.
Axiom proof_of_OSFlagAccept_safety_wit_6 : OSFlagAccept_safety_wit_6.
Axiom proof_of_OSFlagAccept_safety_wit_7 : OSFlagAccept_safety_wit_7.
Axiom proof_of_OSFlagAccept_safety_wit_8 : OSFlagAccept_safety_wit_8.
Axiom proof_of_OSFlagAccept_safety_wit_9 : OSFlagAccept_safety_wit_9.
Axiom proof_of_OSFlagAccept_safety_wit_10 : OSFlagAccept_safety_wit_10.
Axiom proof_of_OSFlagAccept_safety_wit_11 : OSFlagAccept_safety_wit_11.
Axiom proof_of_OSFlagAccept_safety_wit_12 : OSFlagAccept_safety_wit_12.
Axiom proof_of_OSFlagAccept_safety_wit_13 : OSFlagAccept_safety_wit_13.
Axiom proof_of_OSFlagAccept_safety_wit_14 : OSFlagAccept_safety_wit_14.
Axiom proof_of_OSFlagAccept_entail_wit_1 : OSFlagAccept_entail_wit_1.
Axiom proof_of_OSFlagAccept_entail_wit_2_1 : OSFlagAccept_entail_wit_2_1.
Axiom proof_of_OSFlagAccept_entail_wit_2_2 : OSFlagAccept_entail_wit_2_2.
Axiom proof_of_OSFlagAccept_entail_wit_3_1 : OSFlagAccept_entail_wit_3_1.
Axiom proof_of_OSFlagAccept_entail_wit_3_2 : OSFlagAccept_entail_wit_3_2.
Axiom proof_of_OSFlagAccept_entail_wit_3_3 : OSFlagAccept_entail_wit_3_3.
Axiom proof_of_OSFlagAccept_entail_wit_4_1 : OSFlagAccept_entail_wit_4_1.
Axiom proof_of_OSFlagAccept_entail_wit_4_2 : OSFlagAccept_entail_wit_4_2.
Axiom proof_of_OSFlagAccept_entail_wit_4_3 : OSFlagAccept_entail_wit_4_3.
Axiom proof_of_OSFlagAccept_entail_wit_5_1 : OSFlagAccept_entail_wit_5_1.
Axiom proof_of_OSFlagAccept_entail_wit_5_2 : OSFlagAccept_entail_wit_5_2.
Axiom proof_of_OSFlagAccept_entail_wit_5_3 : OSFlagAccept_entail_wit_5_3.
Axiom proof_of_OSFlagAccept_entail_wit_6_1 : OSFlagAccept_entail_wit_6_1.
Axiom proof_of_OSFlagAccept_entail_wit_6_2 : OSFlagAccept_entail_wit_6_2.
Axiom proof_of_OSFlagAccept_entail_wit_6_3 : OSFlagAccept_entail_wit_6_3.
Axiom proof_of_OSFlagAccept_entail_wit_7 : OSFlagAccept_entail_wit_7.
Axiom proof_of_OSFlagAccept_return_wit_1 : OSFlagAccept_return_wit_1.
Axiom proof_of_OSFlagAccept_return_wit_2 : OSFlagAccept_return_wit_2.
Axiom proof_of_OSFlagAccept_return_wit_3 : OSFlagAccept_return_wit_3.
Axiom proof_of_OSFlagAccept_return_wit_4 : OSFlagAccept_return_wit_4.
Axiom proof_of_OSFlagAccept_return_wit_5 : OSFlagAccept_return_wit_5.
Axiom proof_of_OSFlagAccept_return_wit_6 : OSFlagAccept_return_wit_6.
Axiom proof_of_OSFlagAccept_return_wit_7 : OSFlagAccept_return_wit_7.
Axiom proof_of_OSFlagAccept_partial_solve_wit_1_pure : OSFlagAccept_partial_solve_wit_1_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_1 : OSFlagAccept_partial_solve_wit_1.
Axiom proof_of_OSFlagAccept_partial_solve_wit_2 : OSFlagAccept_partial_solve_wit_2.
Axiom proof_of_OSFlagAccept_partial_solve_wit_3_pure : OSFlagAccept_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_3 : OSFlagAccept_partial_solve_wit_3.
Axiom proof_of_OSFlagAccept_partial_solve_wit_4_pure : OSFlagAccept_partial_solve_wit_4_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_4 : OSFlagAccept_partial_solve_wit_4.
Axiom proof_of_OSFlagAccept_partial_solve_wit_5 : OSFlagAccept_partial_solve_wit_5.
Axiom proof_of_OSFlagAccept_partial_solve_wit_6 : OSFlagAccept_partial_solve_wit_6.
Axiom proof_of_OSFlagAccept_partial_solve_wit_7_pure : OSFlagAccept_partial_solve_wit_7_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_7 : OSFlagAccept_partial_solve_wit_7.
Axiom proof_of_OSFlagAccept_partial_solve_wit_8_pure : OSFlagAccept_partial_solve_wit_8_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_8 : OSFlagAccept_partial_solve_wit_8.
Axiom proof_of_OSFlagAccept_partial_solve_wit_9_pure : OSFlagAccept_partial_solve_wit_9_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_9 : OSFlagAccept_partial_solve_wit_9.
Axiom proof_of_OSFlagAccept_partial_solve_wit_10_pure : OSFlagAccept_partial_solve_wit_10_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_10 : OSFlagAccept_partial_solve_wit_10.
Axiom proof_of_OSFlagAccept_partial_solve_wit_11_pure : OSFlagAccept_partial_solve_wit_11_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_11 : OSFlagAccept_partial_solve_wit_11.
Axiom proof_of_OSFlagAccept_partial_solve_wit_12_pure : OSFlagAccept_partial_solve_wit_12_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_12 : OSFlagAccept_partial_solve_wit_12.
Axiom proof_of_OSFlagAccept_partial_solve_wit_13_pure : OSFlagAccept_partial_solve_wit_13_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_13 : OSFlagAccept_partial_solve_wit_13.
Axiom proof_of_OSFlagAccept_partial_solve_wit_14_pure : OSFlagAccept_partial_solve_wit_14_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_14 : OSFlagAccept_partial_solve_wit_14.
Axiom proof_of_OSFlagAccept_partial_solve_wit_15_pure : OSFlagAccept_partial_solve_wit_15_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_15 : OSFlagAccept_partial_solve_wit_15.
Axiom proof_of_OSFlagAccept_partial_solve_wit_16_pure : OSFlagAccept_partial_solve_wit_16_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_16 : OSFlagAccept_partial_solve_wit_16.
Axiom proof_of_OSFlagAccept_partial_solve_wit_17_pure : OSFlagAccept_partial_solve_wit_17_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_17 : OSFlagAccept_partial_solve_wit_17.
Axiom proof_of_OSFlagAccept_partial_solve_wit_18_pure : OSFlagAccept_partial_solve_wit_18_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_18 : OSFlagAccept_partial_solve_wit_18.
Axiom proof_of_OSFlagAccept_partial_solve_wit_19_pure : OSFlagAccept_partial_solve_wit_19_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_19 : OSFlagAccept_partial_solve_wit_19.
Axiom proof_of_OSFlagAccept_partial_solve_wit_20_pure : OSFlagAccept_partial_solve_wit_20_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_20 : OSFlagAccept_partial_solve_wit_20.
Axiom proof_of_OSFlagAccept_partial_solve_wit_21_pure : OSFlagAccept_partial_solve_wit_21_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_21 : OSFlagAccept_partial_solve_wit_21.
Axiom proof_of_OSFlagAccept_partial_solve_wit_22_pure : OSFlagAccept_partial_solve_wit_22_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_22 : OSFlagAccept_partial_solve_wit_22.
Axiom proof_of_OSFlagAccept_partial_solve_wit_23_pure : OSFlagAccept_partial_solve_wit_23_pure.
Axiom proof_of_OSFlagAccept_partial_solve_wit_23 : OSFlagAccept_partial_solve_wit_23.
Axiom proof_of_OSFlagAccept_which_implies_wit_1 : OSFlagAccept_which_implies_wit_1.
Axiom proof_of_OSFlagAccept_which_implies_wit_2 : OSFlagAccept_which_implies_wit_2.
Axiom proof_of_OSFlagAccept_which_implies_wit_3 : OSFlagAccept_which_implies_wit_3.
Axiom proof_of_OSFlagAccept_which_implies_wit_4 : OSFlagAccept_which_implies_wit_4.
Axiom proof_of_OSFlagAccept_which_implies_wit_5 : OSFlagAccept_which_implies_wit_5.
Axiom proof_of_OSFlagAccept_which_implies_wit_6 : OSFlagAccept_which_implies_wit_6.
Axiom proof_of_OSFlagAccept_which_implies_wit_7 : OSFlagAccept_which_implies_wit_7.
Axiom proof_of_OSFlagAccept_which_implies_wit_8 : OSFlagAccept_which_implies_wit_8.
Axiom proof_of_OSFlagAccept_which_implies_wit_9 : OSFlagAccept_which_implies_wit_9.
Axiom proof_of_OSFlagAccept_which_implies_wit_10 : OSFlagAccept_which_implies_wit_10.
Axiom proof_of_OSFlagAccept_which_implies_wit_11 : OSFlagAccept_which_implies_wit_11.
Axiom proof_of_OSFlagAccept_which_implies_wit_12 : OSFlagAccept_which_implies_wit_12.
Axiom proof_of_OSFlagAccept_which_implies_wit_13 : OSFlagAccept_which_implies_wit_13.
Axiom proof_of_OSFlagAccept_which_implies_wit_14 : OSFlagAccept_which_implies_wit_14.

End VC_Correct.
