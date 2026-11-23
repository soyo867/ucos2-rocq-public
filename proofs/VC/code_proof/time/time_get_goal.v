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
Require Import Ucos2Verify.VC.code.time.spec.time_get_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSTimeGet -----*)

Definition OSTimeGet_safety_wit_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH3 : (time_get_safe critical sg invocation before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ticks" ) )) # UInt  |->_)
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeGet_safety_wit_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 <= (time_get (entry_2)))) (PreH4 : ((time_get (entry_2)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ticks" ) )) # UInt  |-> (time_get (entry_2)))
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeGet_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : (0 <= (time_get (entry)))) (PreH4 : ((time_get (entry)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry )
  **  (caller_frame )
|--
  (time_get_api_post platform critical sg invocation origin mask before (time_get (entry)) X )
  **  (caller_frame )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : (0 <= (time_get (entry)))) (PreH4 : ((time_get (entry)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry )
  **  (caller_frame )
|--
  (time_get_api_post platform critical sg invocation origin mask before (time_get (entry)) X )
  **  (caller_frame )
).

Definition OSTimeGet_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : (0 <= (time_get (entry)))) (PreH4 : ((time_get (entry)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry )
  **  (caller_frame )
|--
  (time_get_api_post platform critical sg invocation origin mask before (time_get (entry)) X )
  **  (caller_frame )
.

Definition OSTimeGet_partial_solve_wit_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_safe critical sg invocation before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_safe critical sg invocation before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
.

Definition OSTimeGet_partial_solve_wit_2_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH3 : (time_get_safe critical sg invocation before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ticks" ) )) # UInt  |->_)
  **  (caller_frame )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ”
.

Definition OSTimeGet_partial_solve_wit_2_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH3 : (time_get_safe critical sg invocation before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller_frame )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_safe critical sg invocation before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller_frame )
.

Definition OSTimeGet_partial_solve_wit_2 := OSTimeGet_partial_solve_wit_2_pure -> OSTimeGet_partial_solve_wit_2_aux.

Definition OSTimeGet_partial_solve_wit_3_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 <= (time_get (entry_2)))) (PreH4 : ((time_get (entry_2)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry_2)))
  **  (time_get_read_frame sg entry_2 )
  **  ((( &( "ticks" ) )) # UInt  |-> (time_get (entry_2)))
  **  (caller_frame )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ”
.

Definition OSTimeGet_partial_solve_wit_3_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 <= (time_get (entry_2)))) (PreH4 : ((time_get (entry_2)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry_2)))
  **  (time_get_read_frame sg entry_2 )
  **  (caller_frame )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (0 <= (time_get (entry_2))) ” 
  &&  “ ((time_get (entry_2)) <= UINT_MAX) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_safe critical sg invocation before X ) ”
  &&  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry_2)))
  **  (time_get_read_frame sg entry_2 )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (caller_frame )
.

Definition OSTimeGet_partial_solve_wit_3 := OSTimeGet_partial_solve_wit_3_pure -> OSTimeGet_partial_solve_wit_3_aux.

Definition OSTimeGet_partial_solve_wit_4_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 <= (time_get (entry_2)))) (PreH4 : ((time_get (entry_2)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (UCOS2_inv sg entry_2 )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((( &( "ticks" ) )) # UInt  |-> (time_get (entry_2)))
  **  (caller_frame )
|--
  “ (retval = retval) ”
.

Definition OSTimeGet_partial_solve_wit_4_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH3 : (0 <= (time_get (entry_2)))) (PreH4 : ((time_get (entry_2)) <= UINT_MAX)) (PreH5 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH6 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH7 : (time_get_safe critical sg invocation before X )) ,
  (UCOS2_inv sg entry_2 )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (caller_frame )
|--
  “ (retval = retval) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (0 <= (time_get (entry_2))) ” 
  &&  “ ((time_get (entry_2)) <= UINT_MAX) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_safe critical sg invocation before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller_frame )
.

Definition OSTimeGet_partial_solve_wit_4 := OSTimeGet_partial_solve_wit_4_pure -> OSTimeGet_partial_solve_wit_4_aux.

Definition OSTimeGet_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= (time_get (entry))) ” 
  &&  “ ((time_get (entry)) <= UINT_MAX) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
  **  (time_get_read_frame sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (( &( "OSTime" ) ) = (g_OSTime (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= (time_get (entry))) ” 
  &&  “ ((time_get (entry)) <= UINT_MAX) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
  **  (time_get_read_frame sg entry )
).

Definition OSTimeGet_which_implies_wit_2 := 
(
forall (sg: StableGlobVars) (entry: UCOS2_Verify_State) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) ,
  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
  **  (time_get_read_frame sg entry )
|--
  (UCOS2_inv sg entry )
) \/
(
forall (sg: StableGlobVars) (entry: UCOS2_Verify_State) (PreH1 : ((time_get (entry)) <= UINT_MAX)) (PreH2 : ((time_get (entry)) >= 0)) (PreH3 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) ,
  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
  **  (time_get_read_frame sg entry )
|--
  (UCOS2_inv sg entry )
).

Definition OSTimeGet_which_implies_wit_2_split_goal_spatial := 
forall (sg: StableGlobVars) (entry: UCOS2_Verify_State) (PreH1 : ((time_get (entry)) <= UINT_MAX)) (PreH2 : ((time_get (entry)) >= 0)) (PreH3 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) ,
  ((( &( "OSTime" ) )) # UInt  |-> (time_get (entry)))
  **  (time_get_read_frame sg entry )
|--
  (UCOS2_inv sg entry )
.

Module Type VC_Correct.


Axiom proof_of_OSTimeGet_safety_wit_1 : OSTimeGet_safety_wit_1.
Axiom proof_of_OSTimeGet_safety_wit_2 : OSTimeGet_safety_wit_2.
Axiom proof_of_OSTimeGet_return_wit_1 : OSTimeGet_return_wit_1.
Axiom proof_of_OSTimeGet_partial_solve_wit_1 : OSTimeGet_partial_solve_wit_1.
Axiom proof_of_OSTimeGet_partial_solve_wit_2_pure : OSTimeGet_partial_solve_wit_2_pure.
Axiom proof_of_OSTimeGet_partial_solve_wit_2 : OSTimeGet_partial_solve_wit_2.
Axiom proof_of_OSTimeGet_partial_solve_wit_3_pure : OSTimeGet_partial_solve_wit_3_pure.
Axiom proof_of_OSTimeGet_partial_solve_wit_3 : OSTimeGet_partial_solve_wit_3.
Axiom proof_of_OSTimeGet_partial_solve_wit_4_pure : OSTimeGet_partial_solve_wit_4_pure.
Axiom proof_of_OSTimeGet_partial_solve_wit_4 : OSTimeGet_partial_solve_wit_4.
Axiom proof_of_OSTimeGet_which_implies_wit_1 : OSTimeGet_which_implies_wit_1.
Axiom proof_of_OSTimeGet_which_implies_wit_2 : OSTimeGet_which_implies_wit_2.

End VC_Correct.
