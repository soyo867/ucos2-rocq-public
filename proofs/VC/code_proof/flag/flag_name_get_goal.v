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
Require Import Ucos2Verify.VC.code.flag.spec.flag_name_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSFlagNameGet -----*)

Definition OSFlagNameGet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameGet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameGet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (pname_pre <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameGet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= (flag_name_get_type (image)))) (PreH4 : ((flag_name_get_type (image)) < 256)) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH10 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameGet_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH6 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH9 : ((flag_name_get_type (image)) = 5)) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : ((flag_name_get_type (image)) = 5)) (PreH14 : (old = (Some (previous)))) (PreH15 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH16 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH17 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH20 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH21 : (critical_region_interval critical sg invocation before acquired )) (PreH22 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH26 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagNameGet_entail_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (pname_pre <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (pname_pre <> 0)) (PreH9 : (pgrp_pre <> 0)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
).

Definition OSFlagNameGet_return_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH6 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH9 : ((flag_name_get_type (image)) = 5)) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : ((flag_name_get_type (image)) = 5)) (PreH14 : (old = (Some (previous)))) (PreH15 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH16 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH17 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH20 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH21 : (critical_region_interval critical sg invocation before acquired )) (PreH22 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH26 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((perr_pre) # UChar  |-> 0)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old retval X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH6 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH9 : ((flag_name_get_type (image)) = 5)) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : ((flag_name_get_type (image)) = 5)) (PreH14 : (old = (Some (previous)))) (PreH15 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH16 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH17 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH20 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH21 : (critical_region_interval critical sg invocation before acquired )) (PreH22 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH26 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((perr_pre) # UChar  |-> 0)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old retval X )
).

Definition OSFlagNameGet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH6 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH9 : ((flag_name_get_type (image)) = 5)) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : ((flag_name_get_type (image)) = 5)) (PreH14 : (old = (Some (previous)))) (PreH15 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH16 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH17 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH20 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH21 : (critical_region_interval critical sg invocation before acquired )) (PreH22 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH26 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((perr_pre) # UChar  |-> 0)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old retval X )
.

Definition OSFlagNameGet_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= (flag_name_get_type (image)))) (PreH4 : ((flag_name_get_type (image)) < 256)) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH10 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= (flag_name_get_type (image)))) (PreH4 : ((flag_name_get_type (image)) < 256)) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH10 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
).

Definition OSFlagNameGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= (flag_name_get_type (image)))) (PreH4 : ((flag_name_get_type (image)) < 256)) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH10 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
.

Definition OSFlagNameGet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pgrp_pre <> 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pgrp_pre <> 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
).

Definition OSFlagNameGet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pgrp_pre <> 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
.

Definition OSFlagNameGet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
).

Definition OSFlagNameGet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
.

Definition OSFlagNameGet_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 110)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 110)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
).

Definition OSFlagNameGet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pgrp_pre = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 110)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  (flag_name_get_post platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old 0 X )
.

Definition OSFlagNameGet_partial_solve_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (flag_name_get_pre platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old )
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (flag_name_get_pre platform critical sg invocation origin mask before pgrp_pre pname_pre perr_pre slot raw old )
.

Definition OSFlagNameGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ”
.

Definition OSFlagNameGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
.

Definition OSFlagNameGet_partial_solve_wit_2 := OSFlagNameGet_partial_solve_wit_2_pure -> OSFlagNameGet_partial_solve_wit_2_aux.

Definition OSFlagNameGet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (pname_pre <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ”
.

Definition OSFlagNameGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (pname_pre <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
.

Definition OSFlagNameGet_partial_solve_wit_3 := OSFlagNameGet_partial_solve_wit_3_pure -> OSFlagNameGet_partial_solve_wit_3_aux.

Definition OSFlagNameGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (pname_pre <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ”
.

Definition OSFlagNameGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (pname_pre <> 0)) (PreH4 : (pgrp_pre <> 0)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
.

Definition OSFlagNameGet_partial_solve_wit_4 := OSFlagNameGet_partial_solve_wit_4_pure -> OSFlagNameGet_partial_solve_wit_4_aux.

Definition OSFlagNameGet_partial_solve_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
.

Definition OSFlagNameGet_partial_solve_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (pname_pre <> 0)) (PreH7 : (pgrp_pre <> 0)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (flag_name_get_guarded_private before pgrp_pre pname_pre slot raw )
.

Definition OSFlagNameGet_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ”
.

Definition OSFlagNameGet_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameGet_partial_solve_wit_7 := OSFlagNameGet_partial_solve_wit_7_pure -> OSFlagNameGet_partial_solve_wit_7_aux.

Definition OSFlagNameGet_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH12 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ”
.

Definition OSFlagNameGet_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH12 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameGet_partial_solve_wit_8 := OSFlagNameGet_partial_solve_wit_8_pure -> OSFlagNameGet_partial_solve_wit_8_aux.

Definition OSFlagNameGet_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= (flag_name_get_type (image)))) (PreH4 : ((flag_name_get_type (image)) < 256)) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH10 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSFlagNameGet_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= (flag_name_get_type (image)))) (PreH4 : ((flag_name_get_type (image)) < 256)) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH10 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (0 <= (flag_name_get_type (image))) ” 
  &&  “ ((flag_name_get_type (image)) < 256) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) <> 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameGet_partial_solve_wit_9 := OSFlagNameGet_partial_solve_wit_9_pure -> OSFlagNameGet_partial_solve_wit_9_aux.

Definition OSFlagNameGet_partial_solve_wit_10_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH12 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH7 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH8 : (critical_region_interval critical sg invocation before acquired )) (PreH9 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ ((flag_name_get_type (image)) = 5) ”
).

Definition OSFlagNameGet_partial_solve_wit_10_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH7 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH8 : (critical_region_interval critical sg invocation before acquired )) (PreH9 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ ((flag_name_get_type (image)) = 5) ”
.

Definition OSFlagNameGet_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (PreH1 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH2 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH12 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp_pre image )
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (flag_name_get_name_cell pgrp_pre image )
  **  (task_name_get_output_cell pname_pre old )
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameGet_partial_solve_wit_10 := OSFlagNameGet_partial_solve_wit_10_pure -> OSFlagNameGet_partial_solve_wit_10_aux.

Definition OSFlagNameGet_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) (PreH5 : (old = (Some (previous)))) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH7 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH11 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH17 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH18 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ”
.

Definition OSFlagNameGet_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) (PreH5 : (old = (Some (previous)))) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH7 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH11 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH17 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH18 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  ((&((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  (flag_name_get_read_frame sg acquired pgrp_pre slot image )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameGet_partial_solve_wit_11 := OSFlagNameGet_partial_solve_wit_11_pure -> OSFlagNameGet_partial_solve_wit_11_aux.

Definition OSFlagNameGet_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH8 : ((flag_name_get_type (image)) = 5)) (PreH9 : (old = (Some (previous)))) (PreH10 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH11 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH21 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH22 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH23 : (critical_region_interval critical sg invocation before acquired )) (PreH24 : (interrupt_saved_value mask cpu_sr )) (PreH25 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
.

Definition OSFlagNameGet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) (PreH5 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH8 : ((flag_name_get_type (image)) = 5)) (PreH9 : (old = (Some (previous)))) (PreH10 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH11 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH12 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH21 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH22 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH23 : (critical_region_interval critical sg invocation before acquired )) (PreH24 : (interrupt_saved_value mask cpu_sr )) (PreH25 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSFlagNameGet_partial_solve_wit_12 := OSFlagNameGet_partial_solve_wit_12_pure -> OSFlagNameGet_partial_solve_wit_12_aux.

Definition OSFlagNameGet_partial_solve_wit_13 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((flag_name_get_type (image)) = 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH10 : ((flag_name_get_type (image)) = 5)) (PreH11 : (old = (Some (previous)))) (PreH12 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH13 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH14 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (UCOS2_state_inv sg acquired )) (PreH22 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH23 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH24 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (interrupt_saved_value mask cpu_sr )) (PreH27 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
.

Definition OSFlagNameGet_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((flag_name_get_type (image)) = 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH10 : ((flag_name_get_type (image)) = 5)) (PreH11 : (old = (Some (previous)))) (PreH12 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH13 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH14 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (UCOS2_state_inv sg acquired )) (PreH22 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH23 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH24 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (interrupt_saved_value mask cpu_sr )) (PreH27 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp_pre perr_pre slot raw image chars )
  **  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ ((flag_name_get_name (image)) = (flag_name_get_name (image))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
.

Definition OSFlagNameGet_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH6 : ((flag_name_get_type (image)) = 5)) (PreH7 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH10 : ((flag_name_get_type (image)) = 5)) (PreH11 : (old = (Some (previous)))) (PreH12 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH13 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH14 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH17 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (UCOS2_state_inv sg acquired )) (PreH22 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH23 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH24 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (interrupt_saved_value mask cpu_sr )) (PreH27 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp_pre perr_pre slot raw image chars )
  **  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  “ ((flag_name_get_name (image)) = (flag_name_get_name (image))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp_pre perr_pre slot raw image chars )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
.

Definition OSFlagNameGet_partial_solve_wit_14 := OSFlagNameGet_partial_solve_wit_14_pure -> OSFlagNameGet_partial_solve_wit_14_aux.

Definition OSFlagNameGet_partial_solve_wit_15 := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH7 : ((flag_name_get_type (image)) = 5)) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH11 : ((flag_name_get_type (image)) = 5)) (PreH12 : (old = (Some (previous)))) (PreH13 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH14 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : (UCOS2_state_inv sg acquired )) (PreH17 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH18 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH24 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH25 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH26 : (critical_region_interval critical sg invocation before acquired )) (PreH27 : (interrupt_saved_value mask cpu_sr )) (PreH28 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp_pre perr_pre slot raw image chars )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  “ (retval = (task_name_get_length ((flag_name_get_name (image))) (chars))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp_pre perr_pre slot raw image chars )
  **  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
.

Definition OSFlagNameGet_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH7 : ((flag_name_get_type (image)) = 5)) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH11 : ((flag_name_get_type (image)) = 5)) (PreH12 : (old = (Some (previous)))) (PreH13 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH14 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : (UCOS2_state_inv sg acquired )) (PreH17 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH18 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH24 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH25 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH26 : (critical_region_interval critical sg invocation before acquired )) (PreH27 : (interrupt_saved_value mask cpu_sr )) (PreH28 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
.

Definition OSFlagNameGet_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH4 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH7 : ((flag_name_get_type (image)) = 5)) (PreH8 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH11 : ((flag_name_get_type (image)) = 5)) (PreH12 : (old = (Some (previous)))) (PreH13 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH14 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH15 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH16 : (UCOS2_state_inv sg acquired )) (PreH17 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH18 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH24 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH25 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH26 : (critical_region_interval critical sg invocation before acquired )) (PreH27 : (interrupt_saved_value mask cpu_sr )) (PreH28 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (retval = (task_name_get_length ((flag_name_get_name (image))) (chars))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
.

Definition OSFlagNameGet_partial_solve_wit_16 := OSFlagNameGet_partial_solve_wit_16_pure -> OSFlagNameGet_partial_solve_wit_16_aux.

Definition OSFlagNameGet_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH6 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH9 : ((flag_name_get_type (image)) = 5)) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : ((flag_name_get_type (image)) = 5)) (PreH14 : (old = (Some (previous)))) (PreH15 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH16 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH17 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH20 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH21 : (critical_region_interval critical sg invocation before acquired )) (PreH22 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH26 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (UCOS2_inv sg acquired )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSFlagNameGet_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pgrp_pre: Z) (X: (FlagNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (previous: Z) (chars: (@list Z)) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH3 : (retval = (task_name_get_length ((flag_name_get_name (image))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH6 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH9 : ((flag_name_get_type (image)) = 5)) (PreH10 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH13 : ((flag_name_get_type (image)) = 5)) (PreH14 : (old = (Some (previous)))) (PreH15 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) (PreH16 : ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5)) (PreH17 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH18 : (UCOS2_state_inv sg acquired )) (PreH19 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH20 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH21 : (critical_region_interval critical sg invocation before acquired )) (PreH22 : (flag_name_get_selected sg acquired pgrp_pre slot raw image )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH26 : ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X )) ,
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (retval = (task_name_get_length ((flag_name_get_name (image))) (chars))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ” 
  &&  “ ((unsigned_last_nbits ((flag_name_get_type (image))) (32)) = 5) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp_pre slot raw image ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_addresses sg pgrp_pre ( &( "OSIntNesting" ) ) &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp_pre)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ ((flag_name_get_early_error (pgrp_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp_pre pname_pre slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (flag_name_get_safe critical sg invocation pgrp_pre pname_pre slot raw before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp_pre slot raw )
  **  ((perr_pre) # UChar  |->_)
  **  ((pname_pre) # Ptr  |-> (flag_name_get_name (image)))
.

Definition OSFlagNameGet_partial_solve_wit_17 := OSFlagNameGet_partial_solve_wit_17_pure -> OSFlagNameGet_partial_solve_wit_17_aux.

Definition OSFlagNameGet_which_implies_wit_1 := 
(
forall (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) (pname: Z) (pgrp: Z) ,
  (flag_name_get_pre platform critical sg invocation origin mask before pgrp pname perr slot raw old )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp pname slot raw old ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr) # UChar  |->_)
  **  (task_name_get_output_cell pname old )
  **  (flag_name_get_guarded_private before pgrp pname slot raw )
) \/
(
forall (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) (pname: Z) (pgrp: Z) ,
  (flag_name_get_pre platform critical sg invocation origin mask before pgrp pname perr slot raw old )
|--
  EX (x: Z) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp pname slot raw old ) ”
  &&  ((perr) # UChar  |-> x)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  (task_name_get_output_cell pname old )
  **  (flag_name_get_guarded_private before pgrp pname slot raw )
).

Definition OSFlagNameGet_which_implies_wit_2 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
).

Definition OSFlagNameGet_which_implies_wit_2_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
.

Definition OSFlagNameGet_which_implies_wit_3 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (task_name_get_closed platform critical sg invocation origin mask before )
).

Definition OSFlagNameGet_which_implies_wit_3_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (task_name_get_closed platform critical sg invocation origin mask before )
.

Definition OSFlagNameGet_which_implies_wit_4 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
).

Definition OSFlagNameGet_which_implies_wit_4_split_goal_1 := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ”
.

Definition OSFlagNameGet_which_implies_wit_4_split_goal_2 := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (0 <= (task_name_get_nesting (before))) ”
.

Definition OSFlagNameGet_which_implies_wit_4_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (task_name_get_closed platform critical sg invocation origin mask before )
.

Definition OSFlagNameGet_which_implies_wit_5 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSFlagNameGet_which_implies_wit_5_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSFlagNameGet_which_implies_wit_6 := 
(
forall (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (pgrp: Z) (pname: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((flag_name_get_early_error (pgrp) (pname) ((task_name_get_nesting (before)))) = None)) (PreH4 : (flag_name_get_access critical sg invocation before pgrp pname slot raw old )) (PreH5 : (critical_region_interval critical sg invocation before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
|--
  EX (image: FlagGroupImage) ,
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp) (pname) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp pname slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp slot raw image ) ”
  &&  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
) \/
(
forall (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (pgrp: Z) (pname: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((flag_name_get_early_error (pgrp) (pname) ((task_name_get_nesting (before)))) = None)) (PreH4 : (flag_name_get_access critical sg invocation before pgrp pname slot raw old )) (PreH5 : (critical_region_interval critical sg invocation before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
|--
  EX (image: FlagGroupImage) ,
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((flag_name_get_early_error (pgrp) (pname) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (flag_name_get_access critical sg invocation before pgrp pname slot raw old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp slot raw image ) ”
  &&  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
).

Definition OSFlagNameGet_which_implies_wit_7 := 
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (0 <= (flag_name_get_type (image))) ” 
  &&  “ ((flag_name_get_type (image)) < 256) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp slot raw image ) ”
  &&  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
) \/
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  “ ((flag_name_get_type (image)) < 256) ” 
  &&  “ (0 <= (flag_name_get_type (image))) ”
  &&  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
).

Definition OSFlagNameGet_which_implies_wit_7_split_goal_1 := 
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  “ ((flag_name_get_type (image)) < 256) ”
.

Definition OSFlagNameGet_which_implies_wit_7_split_goal_2 := 
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  “ (0 <= (flag_name_get_type (image))) ”
.

Definition OSFlagNameGet_which_implies_wit_7_split_goal_spatial := 
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  (flag_name_get_name_cell pgrp image )
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
.

Definition OSFlagNameGet_which_implies_wit_8 := 
(
forall (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (pname: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) (PreH5 : ((flag_name_get_early_error (pgrp) (pname) ((task_name_get_nesting (before)))) = None)) (PreH6 : (flag_name_get_access critical sg invocation before pgrp pname slot raw old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) ,
  (flag_name_get_name_cell pgrp image )
  **  (task_name_get_output_cell pname old )
|--
  EX (chars: (@list Z))  (previous: Z) ,
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
  &&  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  ((pname) # Ptr  |-> previous)
) \/
(
forall (old: (@option Z)) (raw: FlagGroupImage) (slot: (@option Z)) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (pname: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) (PreH5 : ((flag_name_get_early_error (pgrp) (pname) ((task_name_get_nesting (before)))) = None)) (PreH6 : (flag_name_get_access critical sg invocation before pgrp pname slot raw old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) ,
  (flag_name_get_name_cell pgrp image )
  **  (task_name_get_output_cell pname old )
|--
  EX (chars: (@list Z))  (previous: Z) ,
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
  &&  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  ((pname) # Ptr  |-> previous)
).

Definition OSFlagNameGet_which_implies_wit_9 := 
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  “ (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (flag_name_get_selected sg acquired pgrp slot raw image ) ” 
  &&  “ ((flag_name_get_type (image)) = 5) ”
  &&  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
) \/
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
).

Definition OSFlagNameGet_which_implies_wit_9_split_goal_spatial := 
forall (raw: FlagGroupImage) (slot: (@option Z)) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (pgrp: Z) (PreH1 : (flag_name_get_addresses sg pgrp ( &( "OSIntNesting" ) ) &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType") &((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName") )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (flag_name_get_selected sg acquired pgrp slot raw image )) (PreH4 : ((flag_name_get_type (image)) = 5)) ,
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flag_name_get_type (image)))
  **  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flag_name_get_name (image)))
  **  (flag_name_get_read_frame sg acquired pgrp slot image )
|--
  (UCOS2_inv sg acquired )
  **  (flag_name_get_private pgrp slot raw )
.

Definition OSFlagNameGet_which_implies_wit_10 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
  &&  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
).

Definition OSFlagNameGet_which_implies_wit_10_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
.

Definition OSFlagNameGet_which_implies_wit_11 := 
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (pgrp: Z) (cpu_sr: Z) (perr: Z) ,
  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
|--
  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp perr slot raw image chars )
) \/
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (pgrp: Z) (cpu_sr: Z) (perr: Z) ,
  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
|--
  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp perr slot raw image chars )
).

Definition OSFlagNameGet_which_implies_wit_11_split_goal_spatial := 
forall (raw: FlagGroupImage) (slot: (@option Z)) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (pgrp: Z) (cpu_sr: Z) (perr: Z) ,
  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
|--
  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp perr slot raw image chars )
.

Definition OSFlagNameGet_which_implies_wit_12 := 
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (perr: Z) (pgrp: Z) (cpu_sr: Z) ,
  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp perr slot raw image chars )
|--
  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
) \/
(
forall (raw: FlagGroupImage) (slot: (@option Z)) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (perr: Z) (pgrp: Z) (cpu_sr: Z) ,
  (flag_name_get_call_frame platform critical sg invocation origin cpu_sr acquired pgrp perr slot raw image chars )
|--
  EX (x: Z) ,
  ((perr) # UChar  |-> x)
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
  **  (flag_name_get_private pgrp slot raw )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
).

Definition OSFlagNameGet_which_implies_wit_13 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) ,
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars ) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) ,
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
|--
  (UCOS2_inv sg acquired )
).

Definition OSFlagNameGet_which_implies_wit_13_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (image: FlagGroupImage) (chars: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_readable (task_name_get_names (acquired)) (flag_name_get_name (image)) chars )) ,
  (task_name_get_name_bytes (flag_name_get_name (image)) chars )
  **  (task_name_get_name_frame sg acquired (flag_name_get_name (image)) chars )
|--
  (UCOS2_inv sg acquired )
.

Definition OS_StrLen_derive_flag_name_get_spec_by_exact_frame_spec := 
forall (psrc_pre: Z) (frame_flag_name_get_spec: Assertion) (chars_flag_name_get_spec: (@list Z)) (names_flag_name_get_spec: NameResourceState) (entry_flag_name_get_spec: Z) ,
  “ (psrc_pre = entry_flag_name_get_spec) ” 
  &&  “ (task_name_get_readable names_flag_name_get_spec entry_flag_name_get_spec chars_flag_name_get_spec ) ”
  &&  (task_name_get_name_bytes entry_flag_name_get_spec chars_flag_name_get_spec )
  **  (frame_flag_name_get_spec )
|--
EX (entry_exact_frame_spec: Z) (base_exact_frame_spec: Z) (names_exact_frame_spec: NameResourceState) (chars_exact_frame_spec: (@list Z)) (frame_exact_frame_spec: Assertion) ,
  ((“ (psrc_pre = entry_exact_frame_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_exact_frame_spec) ” 
  &&  “ (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec ) ”
  &&  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec ))
  ||
  (“ (psrc_pre = entry_exact_frame_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_exact_frame_spec )))
  **
  (((EX retval_2,
  “ (entry_exact_frame_spec = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (frame_exact_frame_spec ))
  ||
  (EX retval_2,
  “ (entry_exact_frame_spec <> 0) ” 
  &&  “ (entry_exact_frame_spec = base_exact_frame_spec) ” 
  &&  “ (os_strlen_result chars_exact_frame_spec retval_2 ) ”
  &&  (os_strlen_bytes entry_exact_frame_spec chars_exact_frame_spec )
  **  (frame_exact_frame_spec )))
  -*
  (EX retval,
  “ (retval = (task_name_get_length (entry_flag_name_get_spec) (chars_flag_name_get_spec))) ”
  &&  (task_name_get_name_bytes entry_flag_name_get_spec chars_flag_name_get_spec )
  **  (frame_flag_name_get_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSFlagNameGet_safety_wit_1 : OSFlagNameGet_safety_wit_1.
Axiom proof_of_OSFlagNameGet_safety_wit_2 : OSFlagNameGet_safety_wit_2.
Axiom proof_of_OSFlagNameGet_safety_wit_3 : OSFlagNameGet_safety_wit_3.
Axiom proof_of_OSFlagNameGet_safety_wit_4 : OSFlagNameGet_safety_wit_4.
Axiom proof_of_OSFlagNameGet_safety_wit_5 : OSFlagNameGet_safety_wit_5.
Axiom proof_of_OSFlagNameGet_entail_wit_1 : OSFlagNameGet_entail_wit_1.
Axiom proof_of_OSFlagNameGet_return_wit_1 : OSFlagNameGet_return_wit_1.
Axiom proof_of_OSFlagNameGet_return_wit_2 : OSFlagNameGet_return_wit_2.
Axiom proof_of_OSFlagNameGet_return_wit_3 : OSFlagNameGet_return_wit_3.
Axiom proof_of_OSFlagNameGet_return_wit_4 : OSFlagNameGet_return_wit_4.
Axiom proof_of_OSFlagNameGet_return_wit_5 : OSFlagNameGet_return_wit_5.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_1 : OSFlagNameGet_partial_solve_wit_1.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_2_pure : OSFlagNameGet_partial_solve_wit_2_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_2 : OSFlagNameGet_partial_solve_wit_2.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_3_pure : OSFlagNameGet_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_3 : OSFlagNameGet_partial_solve_wit_3.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_4_pure : OSFlagNameGet_partial_solve_wit_4_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_4 : OSFlagNameGet_partial_solve_wit_4.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_5 : OSFlagNameGet_partial_solve_wit_5.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_6 : OSFlagNameGet_partial_solve_wit_6.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_7_pure : OSFlagNameGet_partial_solve_wit_7_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_7 : OSFlagNameGet_partial_solve_wit_7.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_8_pure : OSFlagNameGet_partial_solve_wit_8_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_8 : OSFlagNameGet_partial_solve_wit_8.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_9_pure : OSFlagNameGet_partial_solve_wit_9_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_9 : OSFlagNameGet_partial_solve_wit_9.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_10_pure : OSFlagNameGet_partial_solve_wit_10_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_10 : OSFlagNameGet_partial_solve_wit_10.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_11_pure : OSFlagNameGet_partial_solve_wit_11_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_11 : OSFlagNameGet_partial_solve_wit_11.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_12_pure : OSFlagNameGet_partial_solve_wit_12_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_12 : OSFlagNameGet_partial_solve_wit_12.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_13 : OSFlagNameGet_partial_solve_wit_13.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_14_pure : OSFlagNameGet_partial_solve_wit_14_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_14 : OSFlagNameGet_partial_solve_wit_14.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_15 : OSFlagNameGet_partial_solve_wit_15.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_16_pure : OSFlagNameGet_partial_solve_wit_16_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_16 : OSFlagNameGet_partial_solve_wit_16.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_17_pure : OSFlagNameGet_partial_solve_wit_17_pure.
Axiom proof_of_OSFlagNameGet_partial_solve_wit_17 : OSFlagNameGet_partial_solve_wit_17.
Axiom proof_of_OSFlagNameGet_which_implies_wit_1 : OSFlagNameGet_which_implies_wit_1.
Axiom proof_of_OSFlagNameGet_which_implies_wit_2 : OSFlagNameGet_which_implies_wit_2.
Axiom proof_of_OSFlagNameGet_which_implies_wit_3 : OSFlagNameGet_which_implies_wit_3.
Axiom proof_of_OSFlagNameGet_which_implies_wit_4 : OSFlagNameGet_which_implies_wit_4.
Axiom proof_of_OSFlagNameGet_which_implies_wit_5 : OSFlagNameGet_which_implies_wit_5.
Axiom proof_of_OSFlagNameGet_which_implies_wit_6 : OSFlagNameGet_which_implies_wit_6.
Axiom proof_of_OSFlagNameGet_which_implies_wit_7 : OSFlagNameGet_which_implies_wit_7.
Axiom proof_of_OSFlagNameGet_which_implies_wit_8 : OSFlagNameGet_which_implies_wit_8.
Axiom proof_of_OSFlagNameGet_which_implies_wit_9 : OSFlagNameGet_which_implies_wit_9.
Axiom proof_of_OSFlagNameGet_which_implies_wit_10 : OSFlagNameGet_which_implies_wit_10.
Axiom proof_of_OSFlagNameGet_which_implies_wit_11 : OSFlagNameGet_which_implies_wit_11.
Axiom proof_of_OSFlagNameGet_which_implies_wit_12 : OSFlagNameGet_which_implies_wit_12.
Axiom proof_of_OSFlagNameGet_which_implies_wit_13 : OSFlagNameGet_which_implies_wit_13.
Axiom proof_of_OS_StrLen_derive_flag_name_get_spec_by_exact_frame_spec : OS_StrLen_derive_flag_name_get_spec_by_exact_frame_spec.

End VC_Correct.
