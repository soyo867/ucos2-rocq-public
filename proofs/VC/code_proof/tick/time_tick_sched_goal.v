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
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) = 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ False ”
.

Definition OS_Sched_safety_wit_3 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_return_wit_1 := 
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
) \/
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
.

Definition OS_Sched_partial_solve_wit_1 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
.

Definition OS_Sched_partial_solve_wit_2 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_3_pure := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
.

Definition OS_Sched_partial_solve_wit_3_aux := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (UCOS2_inv sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_3 := OS_Sched_partial_solve_wit_3_pure -> OS_Sched_partial_solve_wit_3_aux.

Definition OS_Sched_partial_solve_wit_4_pure := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OS_Sched_partial_solve_wit_4_aux := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((os_sched_ints (before)) <> 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_4 := OS_Sched_partial_solve_wit_4_pure -> OS_Sched_partial_solve_wit_4_aux.

Definition OS_Sched_partial_solve_wit_5_pure := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OS_Sched_partial_solve_wit_5_aux := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : ((os_sched_ints (before)) <> 0)) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : ((os_sched_ints (before)) > 0)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH9 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((os_sched_ints (before)) <> 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Definition OS_Sched_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
|--
  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
).

Definition OS_Sched_which_implies_wit_2_split_goal_1 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
|--
  “ ((os_sched_ints (before)) <= 255) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_2 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
.

Definition OS_Sched_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
|--
  (UCOS2_inv sg before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
|--
  (UCOS2_inv sg before )
).

Definition OS_Sched_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH2 : (UCOS2_state_inv sg before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (time_tick_sched_interrupt_frame sg before )
|--
  (UCOS2_inv sg before )
.

Module Type VC_Correct.


Axiom proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Axiom proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Axiom proof_of_OS_Sched_safety_wit_3 : OS_Sched_safety_wit_3.
Axiom proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Axiom proof_of_OS_Sched_partial_solve_wit_3_pure : OS_Sched_partial_solve_wit_3_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Axiom proof_of_OS_Sched_partial_solve_wit_4_pure : OS_Sched_partial_solve_wit_4_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Axiom proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Axiom proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Axiom proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Axiom proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.

End VC_Correct.
