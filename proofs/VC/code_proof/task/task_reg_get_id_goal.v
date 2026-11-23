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
Require Import Ucos2Verify.VC.code.task.spec.task_reg_get_id_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskRegGetID -----*)

Definition OSTaskRegGetID_safety_wit_1 := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_get_id_safe critical sg invocation before X )) (PreH5 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "id" ) )) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGetID_safety_wit_2 := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_reg_get_id_effect sg entry 1 150 entry )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr_pre) # UChar  |-> 150)
  **  ((( &( "id" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGetID_safety_wit_3 := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (id = (task_reg_get_id_next (entry)))) (PreH5 : (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "id" ) )) # UChar  |-> id)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGetID_entail_wit_1 := 
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_get_id_safe critical sg invocation before X )) (PreH5 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (0 <= (task_reg_get_id_next (entry))) ” 
  &&  “ ((task_reg_get_id_next (entry)) <= 1) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> (task_reg_get_id_next (entry)))
  **  (task_reg_get_id_frame sg entry )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_get_id_safe critical sg invocation before X )) (PreH5 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (0 <= (task_reg_get_id_next (entry))) ” 
  &&  “ ((task_reg_get_id_next (entry)) <= 1) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> (task_reg_get_id_next (entry)))
  **  (task_reg_get_id_frame sg entry )
).

Definition OSTaskRegGetID_entail_wit_2 := 
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_reg_get_id_next (entry_2)) >= 1)) (PreH2 : (task_reg_get_id_safe critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg entry_2 )) (PreH4 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) (PreH5 : (critical_region_interval critical sg invocation before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (0 <= (task_reg_get_id_next (entry_2)))) (PreH8 : ((task_reg_get_id_next (entry_2)) <= 1)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> (task_reg_get_id_next (entry_2)))
  **  (task_reg_get_id_frame sg entry_2 )
  **  ((perr_pre) # UChar  |-> 150)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_get_id_effect sg entry 1 150 entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |-> 150)
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_reg_get_id_next (entry_2)) >= 1)) (PreH2 : (task_reg_get_id_safe critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg entry_2 )) (PreH4 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) (PreH5 : (critical_region_interval critical sg invocation before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (0 <= (task_reg_get_id_next (entry_2)))) (PreH8 : ((task_reg_get_id_next (entry_2)) <= 1)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> (task_reg_get_id_next (entry_2)))
  **  (task_reg_get_id_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_get_id_effect sg entry 1 150 entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
).

Definition OSTaskRegGetID_entail_wit_3 := 
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_reg_get_id_next (entry)) < 1)) (PreH2 : (task_reg_get_id_safe critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (0 <= (task_reg_get_id_next (entry)))) (PreH8 : ((task_reg_get_id_next (entry)) <= 1)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> ((task_reg_get_id_next (entry)) + 1 ))
  **  (task_reg_get_id_frame sg entry )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ ((task_reg_get_id_next (entry)) = (task_reg_get_id_next (entry_2))) ” 
  &&  “ (task_reg_get_id_effect sg entry_2 (task_reg_get_id_next (entry)) 0 (task_reg_get_id_update (entry_2) (((task_reg_get_id_next (entry_2)) + 1 ))) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg (task_reg_get_id_update (entry_2) (((task_reg_get_id_next (entry_2)) + 1 ))) )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_reg_get_id_next (entry)) < 1)) (PreH2 : (task_reg_get_id_safe critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (0 <= (task_reg_get_id_next (entry)))) (PreH8 : ((task_reg_get_id_next (entry)) <= 1)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> ((task_reg_get_id_next (entry)) + 1 ))
  **  (task_reg_get_id_frame sg entry )
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ ((task_reg_get_id_next (entry)) = (task_reg_get_id_next (entry_2))) ” 
  &&  “ (task_reg_get_id_effect sg entry_2 (task_reg_get_id_next (entry)) 0 (task_reg_get_id_update (entry_2) (((task_reg_get_id_next (entry_2)) + 1 ))) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg (task_reg_get_id_update (entry_2) (((task_reg_get_id_next (entry_2)) + 1 ))) )
).

Definition OSTaskRegGetID_return_wit_1 := 
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (id = (task_reg_get_id_next (entry)))) (PreH5 : (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (task_reg_get_id_post platform critical sg invocation origin mask before perr_pre id X )
) \/
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (id = (task_reg_get_id_next (entry)))) (PreH5 : (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (task_reg_get_id_post platform critical sg invocation origin mask before perr_pre id X )
).

Definition OSTaskRegGetID_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (id = (task_reg_get_id_next (entry)))) (PreH5 : (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (task_reg_get_id_post platform critical sg invocation origin mask before perr_pre id X )
.

Definition OSTaskRegGetID_return_wit_2 := 
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_reg_get_id_effect sg entry 1 150 entry )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((perr_pre) # UChar  |-> 150)
|--
  (task_reg_get_id_post platform critical sg invocation origin mask before perr_pre 1 X )
) \/
(
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_reg_get_id_effect sg entry 1 150 entry )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((perr_pre) # UChar  |-> 150)
|--
  (task_reg_get_id_post platform critical sg invocation origin mask before perr_pre 1 X )
).

Definition OSTaskRegGetID_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_reg_get_id_effect sg entry 1 150 entry )) ,
  (task_reg_get_id_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((perr_pre) # UChar  |-> 150)
|--
  (task_reg_get_id_post platform critical sg invocation origin mask before perr_pre 1 X )
.

Definition OSTaskRegGetID_partial_solve_wit_1 := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) ,
  (task_reg_get_id_pre platform critical sg invocation origin mask before perr_pre )
|--
  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) ) ”
  &&  (task_reg_get_id_pre platform critical sg invocation origin mask before perr_pre )
.

Definition OSTaskRegGetID_partial_solve_wit_2 := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_reg_get_id_safe critical sg invocation before X )) (PreH3 : (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (task_reg_get_id_addresses sg ( &( "OSTaskRegNextAvailID" ) ) ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGetID_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_reg_get_id_effect sg entry 1 150 entry )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |-> 150)
  **  ((( &( "id" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskRegGetID_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_reg_get_id_effect sg entry 1 150 entry )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |-> 150)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_get_id_effect sg entry 1 150 entry ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |-> 150)
.

Definition OSTaskRegGetID_partial_solve_wit_3 := OSTaskRegGetID_partial_solve_wit_3_pure -> OSTaskRegGetID_partial_solve_wit_3_aux.

Definition OSTaskRegGetID_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (id = (task_reg_get_id_next (entry)))) (PreH5 : (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "id" ) )) # UChar  |-> id)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskRegGetID_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (PreH1 : (task_reg_get_id_safe critical sg invocation before X )) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (id = (task_reg_get_id_next (entry)))) (PreH5 : (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_reg_get_id_safe critical sg invocation before X ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (id = (task_reg_get_id_next (entry))) ” 
  &&  “ (task_reg_get_id_effect sg entry id 0 (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (task_reg_get_id_update (entry) (((task_reg_get_id_next (entry)) + 1 ))) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGetID_partial_solve_wit_4 := OSTaskRegGetID_partial_solve_wit_4_pure -> OSTaskRegGetID_partial_solve_wit_4_aux.

Definition OSTaskRegGetID_which_implies_wit_1 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) ,
  (task_reg_get_id_pre platform critical sg invocation origin mask before perr )
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr) # UChar  |->_)
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) ,
  (task_reg_get_id_pre platform critical sg invocation origin mask before perr )
|--
  EX (x: Z) ,
  “ (UCOS2_state_inv sg before ) ”
  &&  ((perr) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
).

Module Type VC_Correct.


Axiom proof_of_OSTaskRegGetID_safety_wit_1 : OSTaskRegGetID_safety_wit_1.
Axiom proof_of_OSTaskRegGetID_safety_wit_2 : OSTaskRegGetID_safety_wit_2.
Axiom proof_of_OSTaskRegGetID_safety_wit_3 : OSTaskRegGetID_safety_wit_3.
Axiom proof_of_OSTaskRegGetID_entail_wit_1 : OSTaskRegGetID_entail_wit_1.
Axiom proof_of_OSTaskRegGetID_entail_wit_2 : OSTaskRegGetID_entail_wit_2.
Axiom proof_of_OSTaskRegGetID_entail_wit_3 : OSTaskRegGetID_entail_wit_3.
Axiom proof_of_OSTaskRegGetID_return_wit_1 : OSTaskRegGetID_return_wit_1.
Axiom proof_of_OSTaskRegGetID_return_wit_2 : OSTaskRegGetID_return_wit_2.
Axiom proof_of_OSTaskRegGetID_partial_solve_wit_1 : OSTaskRegGetID_partial_solve_wit_1.
Axiom proof_of_OSTaskRegGetID_partial_solve_wit_2 : OSTaskRegGetID_partial_solve_wit_2.
Axiom proof_of_OSTaskRegGetID_partial_solve_wit_3_pure : OSTaskRegGetID_partial_solve_wit_3_pure.
Axiom proof_of_OSTaskRegGetID_partial_solve_wit_3 : OSTaskRegGetID_partial_solve_wit_3.
Axiom proof_of_OSTaskRegGetID_partial_solve_wit_4_pure : OSTaskRegGetID_partial_solve_wit_4_pure.
Axiom proof_of_OSTaskRegGetID_partial_solve_wit_4 : OSTaskRegGetID_partial_solve_wit_4.
Axiom proof_of_OSTaskRegGetID_which_implies_wit_1 : OSTaskRegGetID_which_implies_wit_1.

End VC_Correct.
