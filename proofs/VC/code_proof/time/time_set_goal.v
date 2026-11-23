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
Require Import Ucos2Verify.VC.code.time.spec.time_set_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSTimeSet -----*)

Definition OSTimeSet_safety_wit_1 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (ticks_pre = requested)) (PreH5 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH6 : (time_set_safe critical sg invocation before requested X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeSet_safety_wit_2 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after )) (PreH2 : (time_set_written critical sg invocation before entry_3 checkpoint requested )) (PreH3 : (0 <= requested)) (PreH4 : (requested <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : ((time_get (entry_2)) >= 0)) (PreH8 : (retval >= 0)) (PreH9 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (ticks_pre = requested)) (PreH14 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH15 : (time_set_safe critical sg invocation before requested X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "ticks" ) )) # UInt  |-> requested)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeSet_entail_wit_1 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (critical_region_interval critical sg invocation before entry )) (PreH3 : (UCOS2_state_inv sg entry )) (PreH4 : (interrupt_saved_value mask retval )) (PreH5 : (ticks_pre = requested)) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_set_safe critical sg invocation before requested X )) ,
  ((( &( "ticks" ) )) # UInt  |-> requested)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (time_set_store_frame platform critical sg invocation origin mask retval before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry_2)))
|--
  “ (0 <= requested) ” 
  &&  “ (requested <= UINT_MAX) ” 
  &&  “ ((time_get (entry_2)) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((time_get (entry_2)) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (ticks_pre = requested) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_set_safe critical sg invocation before requested X ) ”
  &&  ((( &( "ticks" ) )) # UInt  |-> requested)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (time_set_store_frame platform critical sg invocation origin mask retval before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry_2)))
.

Definition OSTimeSet_return_wit_1 := 
(
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (time_set_written critical sg invocation before entry_3 checkpoint requested )) (PreH3 : (0 <= requested)) (PreH4 : (requested <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : ((time_get (entry_2)) >= 0)) (PreH8 : (retval >= 0)) (PreH9 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (ticks_pre = requested)) (PreH14 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH15 : (time_set_safe critical sg invocation before requested X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after_2 )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_set_post critical sg invocation before requested after ) ” 
  &&  “ (time_set_return_safe after X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (time_set_written critical sg invocation before entry_3 checkpoint requested )) (PreH3 : (0 <= requested)) (PreH4 : (requested <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : ((time_get (entry_2)) >= 0)) (PreH8 : (retval >= 0)) (PreH9 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (ticks_pre = requested)) (PreH14 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH15 : (time_set_safe critical sg invocation before requested X )) ,
  TT && emp 
|--
  “ (time_set_return_safe after_2 X ) ” 
  &&  “ (time_set_post critical sg invocation before ticks_pre after_2 ) ”
  &&  emp
).

Definition OSTimeSet_return_wit_1_split_goal_1 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (time_set_written critical sg invocation before entry_3 checkpoint requested )) (PreH3 : (0 <= requested)) (PreH4 : (requested <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : ((time_get (entry_2)) >= 0)) (PreH8 : (retval >= 0)) (PreH9 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (ticks_pre = requested)) (PreH14 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH15 : (time_set_safe critical sg invocation before requested X )) ,
  (time_set_return_safe after_2 X )
.

Definition OSTimeSet_return_wit_1_split_goal_2 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (time_set_written critical sg invocation before entry_3 checkpoint requested )) (PreH3 : (0 <= requested)) (PreH4 : (requested <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : ((time_get (entry_2)) >= 0)) (PreH8 : (retval >= 0)) (PreH9 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (ticks_pre = requested)) (PreH14 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH15 : (time_set_safe critical sg invocation before requested X )) ,
  (time_set_post critical sg invocation before ticks_pre after_2 )
.

Definition OSTimeSet_partial_solve_wit_1 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (ticks_pre = requested)) (PreH2 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH3 : (time_set_safe critical sg invocation before requested X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (ticks_pre = requested) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_set_safe critical sg invocation before requested X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSTimeSet_partial_solve_wit_2_pure := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (ticks_pre = requested)) (PreH5 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH6 : (time_set_safe critical sg invocation before requested X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ”
.

Definition OSTimeSet_partial_solve_wit_2_aux := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (ticks_pre = requested)) (PreH5 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH6 : (time_set_safe critical sg invocation before requested X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (ticks_pre = requested) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_set_safe critical sg invocation before requested X ) ”
  &&  ((( &( "ticks" ) )) # UInt  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
.

Definition OSTimeSet_partial_solve_wit_2 := OSTimeSet_partial_solve_wit_2_pure -> OSTimeSet_partial_solve_wit_2_aux.

Definition OSTimeSet_partial_solve_wit_3_pure := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= requested)) (PreH2 : (requested <= UINT_MAX)) (PreH3 : ((time_get (entry_2)) <= UINT_MAX)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (ticks_pre = requested)) (PreH12 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH13 : (time_set_safe critical sg invocation before requested X )) ,
  ((( &( "ticks" ) )) # UInt  |-> requested)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (time_set_store_frame platform critical sg invocation origin mask retval before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> requested)
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= UINT_MAX) ”
.

Definition OSTimeSet_partial_solve_wit_3_aux := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= requested)) (PreH2 : (requested <= UINT_MAX)) (PreH3 : ((time_get (entry_2)) <= UINT_MAX)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : ((time_get (entry_2)) >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (ticks_pre = requested)) (PreH12 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH13 : (time_set_safe critical sg invocation before requested X )) ,
  (time_set_store_frame platform critical sg invocation origin mask retval before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> requested)
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= UINT_MAX) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= UINT_MAX) ” 
  &&  “ ((time_get (entry_2)) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((time_get (entry_2)) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (ticks_pre = requested) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_set_safe critical sg invocation before requested X ) ”
  &&  (time_set_store_frame platform critical sg invocation origin mask retval before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> requested)
.

Definition OSTimeSet_partial_solve_wit_3 := OSTimeSet_partial_solve_wit_3_pure -> OSTimeSet_partial_solve_wit_3_aux.

Definition OSTimeSet_partial_solve_wit_4 := 
forall (ticks_pre: Z) (X: (unit -> (UCOS2_Verify_State -> Prop))) (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (time_set_written critical sg invocation before entry_3 checkpoint requested )) (PreH2 : (0 <= requested)) (PreH3 : (requested <= UINT_MAX)) (PreH4 : ((time_get (entry_2)) <= UINT_MAX)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : ((time_get (entry_2)) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (UCOS2_state_inv sg entry )) (PreH11 : (interrupt_saved_value mask retval )) (PreH12 : (ticks_pre = requested)) (PreH13 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH14 : (time_set_safe critical sg invocation before requested X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_3 checkpoint )
|--
  “ (time_set_written critical sg invocation before entry_3 checkpoint requested ) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= UINT_MAX) ” 
  &&  “ ((time_get (entry_2)) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((time_get (entry_2)) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (ticks_pre = requested) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_set_safe critical sg invocation before requested X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_3 checkpoint )
.

Definition OSTimeSet_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (critical_region_interval critical sg invocation before entry_2 )) (PreH3 : (UCOS2_state_inv sg entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ”
  &&  (time_set_store_frame platform critical sg invocation origin mask cpu_sr before entry )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (critical_region_interval critical sg invocation before entry_2 )) (PreH3 : (UCOS2_state_inv sg entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ”
  &&  (time_set_store_frame platform critical sg invocation origin mask cpu_sr before entry )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
).

Definition OSTimeSet_which_implies_wit_2 := 
(
forall (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= UINT_MAX)) ,
  (time_set_store_frame platform critical sg invocation origin mask cpu_sr before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> requested)
|--
  EX (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (time_set_written critical sg invocation before entry checkpoint requested ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry checkpoint )
) \/
(
forall (requested: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (requested <= UINT_MAX)) (PreH2 : (requested >= 0)) (PreH3 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH4 : (0 <= requested)) (PreH5 : (requested <= UINT_MAX)) ,
  (time_set_store_frame platform critical sg invocation origin mask cpu_sr before entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> requested)
|--
  EX (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (time_set_written critical sg invocation before entry checkpoint requested ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry checkpoint )
).

Module Type VC_Correct.


Axiom proof_of_OSTimeSet_safety_wit_1 : OSTimeSet_safety_wit_1.
Axiom proof_of_OSTimeSet_safety_wit_2 : OSTimeSet_safety_wit_2.
Axiom proof_of_OSTimeSet_entail_wit_1 : OSTimeSet_entail_wit_1.
Axiom proof_of_OSTimeSet_return_wit_1 : OSTimeSet_return_wit_1.
Axiom proof_of_OSTimeSet_partial_solve_wit_1 : OSTimeSet_partial_solve_wit_1.
Axiom proof_of_OSTimeSet_partial_solve_wit_2_pure : OSTimeSet_partial_solve_wit_2_pure.
Axiom proof_of_OSTimeSet_partial_solve_wit_2 : OSTimeSet_partial_solve_wit_2.
Axiom proof_of_OSTimeSet_partial_solve_wit_3_pure : OSTimeSet_partial_solve_wit_3_pure.
Axiom proof_of_OSTimeSet_partial_solve_wit_3 : OSTimeSet_partial_solve_wit_3.
Axiom proof_of_OSTimeSet_partial_solve_wit_4 : OSTimeSet_partial_solve_wit_4.
Axiom proof_of_OSTimeSet_which_implies_wit_1 : OSTimeSet_which_implies_wit_1.
Axiom proof_of_OSTimeSet_which_implies_wit_2 : OSTimeSet_which_implies_wit_2.

End VC_Correct.
