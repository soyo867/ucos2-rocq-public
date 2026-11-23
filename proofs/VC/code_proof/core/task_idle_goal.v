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
Require Import Ucos2Verify.VC.code.core.spec.task_idle_spec.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_TaskIdle -----*)

Definition OS_TaskIdle_safety_wit_1 := 
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (last_saved: Z) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> last_saved)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OS_TaskIdle_safety_wit_2 := 
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH5 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskIdle_safety_wit_3 := 
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (retval: Z) (acquired_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (restored: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint restored )) (PreH2 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask retval before acquired_2 checkpoint )) (PreH3 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (interrupt_saved_value mask retval )) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH8 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (mutex_query_closed platform critical sg invocation origin mask restored )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskIdle_entail_wit_1 := 
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) ,
  (mutex_query_closed platform critical sg invocation origin initial_mask initial )
|--
  EX (history: (@list TaskIdleIteration))  (mask: Z)  (before: UCOS2_Verify_State) ,
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) ,
  TT && emp 
|--
  EX (history: (@list TaskIdleIteration)) ,
  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history initial_mask initial ) ”
  &&  emp
).

Definition OS_TaskIdle_entail_wit_2 := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (retval: Z) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (restored_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint restored_2 )) (PreH2 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask retval before acquired checkpoint )) (PreH3 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH4 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH5 : (UCOS2_state_inv sg acquired_2 )) (PreH6 : (interrupt_saved_value mask retval )) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH8 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (mutex_query_closed platform critical sg invocation origin mask restored_2 )
|--
  EX (restored: UCOS2_Verify_State) ,
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask retval before acquired checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint restored ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask restored )
.

Definition OS_TaskIdle_entail_wit_3 := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history_2: (@list TaskIdleIteration)) (mask_2: Z) (before_2: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (saved: Z) (restored: UCOS2_Verify_State) (next_mask: Z) (after: UCOS2_Verify_State) (extended: (@list TaskIdleIteration)) (next_mask_2: Z) (after_2: UCOS2_Verify_State) (PreH1 : (task_idle_prefix critical hook sg invocation origin initial_mask initial extended next_mask_2 after_2 )) (PreH2 : (task_idle_hook_returns hook sg invocation origin mask_2 restored next_mask after )) (PreH3 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH4 : (task_idle_written critical hook sg invocation origin initial_mask initial history_2 mask_2 saved before_2 acquired checkpoint )) (PreH5 : (critical_region_interval critical sg invocation checkpoint restored )) ,
  (mutex_query_closed platform critical sg invocation origin next_mask_2 after_2 )
|--
  EX (history: (@list TaskIdleIteration))  (mask: Z)  (before: UCOS2_Verify_State) ,
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OS_TaskIdle_partial_solve_wit_1 := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OS_TaskIdle_partial_solve_wit_2_pure := 
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH5 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ”
.

Definition OS_TaskIdle_partial_solve_wit_2_aux := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH5 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
.

Definition OS_TaskIdle_partial_solve_wit_2 := OS_TaskIdle_partial_solve_wit_2_pure -> OS_TaskIdle_partial_solve_wit_2_aux.

Definition OS_TaskIdle_partial_solve_wit_3_pure := 
(
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH3 : (UCOS2_state_inv sg acquired_2 )) (PreH4 : (interrupt_saved_value mask retval )) (PreH5 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH6 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask retval before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)))
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
|--
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) = (task_idle_counter_after (acquired))) ”
) \/
(
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) >= 0)) (PreH4 : (retval >= 0)) (PreH5 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH6 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH7 : (UCOS2_state_inv sg acquired_2 )) (PreH8 : (interrupt_saved_value mask retval )) (PreH9 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH10 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask retval before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)))
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
|--
  “ ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) = (task_idle_counter_after (acquired))) ”
).

Definition OS_TaskIdle_partial_solve_wit_3_pure_split_goal_1 := 
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) >= 0)) (PreH4 : (retval >= 0)) (PreH5 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH6 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH7 : (UCOS2_state_inv sg acquired_2 )) (PreH8 : (interrupt_saved_value mask retval )) (PreH9 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH10 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask retval before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)))
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
|--
  “ ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) = (task_idle_counter_after (acquired))) ”
.

Definition OS_TaskIdle_partial_solve_wit_3_aux := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH3 : (UCOS2_state_inv sg acquired_2 )) (PreH4 : (interrupt_saved_value mask retval )) (PreH5 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH6 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask retval before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)))
|--
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ ((unsigned_last_nbits (((task_idle_counter (acquired)) + 1 )) (32)) = (task_idle_counter_after (acquired))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired_2 ) ” 
  &&  “ (UCOS2_state_inv sg acquired_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ”
  &&  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask retval before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_idle_counter_after (acquired)))
.

Definition OS_TaskIdle_partial_solve_wit_3 := OS_TaskIdle_partial_solve_wit_3_pure -> OS_TaskIdle_partial_solve_wit_3_aux.

Definition OS_TaskIdle_partial_solve_wit_4 := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (retval: Z) (acquired_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask retval before acquired_2 checkpoint )) (PreH2 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH7 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval acquired_2 checkpoint )
|--
  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask retval before acquired_2 checkpoint ) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval acquired_2 checkpoint )
.

Definition OS_TaskIdle_partial_solve_wit_5 := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (saved: Z) (restored: UCOS2_Verify_State) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint )) (PreH3 : (critical_region_interval critical sg invocation checkpoint restored )) ,
  (mutex_query_closed platform critical sg invocation origin mask restored )
|--
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint restored ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask restored )
.

Definition OS_TaskIdle_partial_solve_wit_6_pure := 
forall (p_arg_pre: Z) (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (saved: Z) (restored: UCOS2_Verify_State) (next_mask: Z) (after: UCOS2_Verify_State) (PreH1 : (task_idle_hook_returns hook sg invocation origin mask restored next_mask after )) (PreH2 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH3 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint )) (PreH4 : (critical_region_interval critical sg invocation checkpoint restored )) ,
  (mutex_query_closed platform critical sg invocation origin next_mask after )
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint restored ) ” 
  &&  “ (task_idle_hook_returns hook sg invocation origin mask restored next_mask after ) ”
.

Definition OS_TaskIdle_partial_solve_wit_6_aux := 
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (saved: Z) (restored: UCOS2_Verify_State) (next_mask: Z) (after: UCOS2_Verify_State) (PreH1 : (task_idle_hook_returns hook sg invocation origin mask restored next_mask after )) (PreH2 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH3 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint )) (PreH4 : (critical_region_interval critical sg invocation checkpoint restored )) ,
  (mutex_query_closed platform critical sg invocation origin next_mask after )
|--
  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint restored ) ” 
  &&  “ (task_idle_hook_returns hook sg invocation origin mask restored next_mask after ) ” 
  &&  “ (task_idle_hook_returns hook sg invocation origin mask restored next_mask after ) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ” 
  &&  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint ) ” 
  &&  “ (critical_region_interval critical sg invocation checkpoint restored ) ”
  &&  (mutex_query_closed platform critical sg invocation origin next_mask after )
.

Definition OS_TaskIdle_partial_solve_wit_6 := OS_TaskIdle_partial_solve_wit_6_pure -> OS_TaskIdle_partial_solve_wit_6_aux.

Definition OS_TaskIdle_which_implies_wit_1 := 
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) (PreH3 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH4 : (UCOS2_state_inv sg acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ”
  &&  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask cpu_sr before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_idle_counter (acquired)))
) \/
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH2 : (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before )) (PreH3 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH4 : (UCOS2_state_inv sg acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg))) ”
  &&  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask cpu_sr before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_idle_counter (acquired)))
).

Definition OS_TaskIdle_which_implies_wit_2 := 
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) ,
  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask cpu_sr before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_idle_counter_after (acquired)))
|--
  EX (checkpoint: UCOS2_Verify_State) ,
  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask cpu_sr before acquired checkpoint ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr acquired checkpoint )
) \/
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_idle_counter_after (acquired)) <= UINT_MAX)) (PreH2 : ((task_idle_counter_after (acquired)) >= 0)) (PreH3 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) ,
  (task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask cpu_sr before acquired )
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_idle_counter_after (acquired)))
|--
  EX (checkpoint: UCOS2_Verify_State) ,
  “ (task_idle_written critical hook sg invocation origin initial_mask initial history mask cpu_sr before acquired checkpoint ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr acquired checkpoint )
).

Definition OS_TaskIdle_which_implies_wit_3 := 
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (saved: Z) (restored: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (next_mask_2: Z) (PreH1 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint )) (PreH2 : (critical_region_interval critical sg invocation checkpoint restored )) (PreH3 : (task_idle_hook_returns hook sg invocation origin mask restored next_mask_2 after_2 )) ,
  (mutex_query_closed platform critical sg invocation origin next_mask_2 after_2 )
|--
  EX (extended: (@list TaskIdleIteration))  (next_mask: Z)  (after: UCOS2_Verify_State) ,
  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial extended next_mask after ) ”
  &&  (mutex_query_closed platform critical sg invocation origin next_mask after )
) \/
(
forall (initial: UCOS2_Verify_State) (initial_mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (hook: TaskIdleHookRelation) (critical: CriticalRegionResources) (history: (@list TaskIdleIteration)) (mask: Z) (before: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (saved: Z) (restored: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (next_mask_2: Z) (PreH1 : (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired checkpoint )) (PreH2 : (critical_region_interval critical sg invocation checkpoint restored )) (PreH3 : (task_idle_hook_returns hook sg invocation origin mask restored next_mask_2 after_2 )) ,
  TT && emp 
|--
  EX (extended: (@list TaskIdleIteration)) ,
  “ (task_idle_prefix critical hook sg invocation origin initial_mask initial extended next_mask_2 after_2 ) ”
  &&  emp
).

Module Type VC_Correct.


Axiom proof_of_OS_TaskIdle_safety_wit_1 : OS_TaskIdle_safety_wit_1.
Axiom proof_of_OS_TaskIdle_safety_wit_2 : OS_TaskIdle_safety_wit_2.
Axiom proof_of_OS_TaskIdle_safety_wit_3 : OS_TaskIdle_safety_wit_3.
Axiom proof_of_OS_TaskIdle_entail_wit_1 : OS_TaskIdle_entail_wit_1.
Axiom proof_of_OS_TaskIdle_entail_wit_2 : OS_TaskIdle_entail_wit_2.
Axiom proof_of_OS_TaskIdle_entail_wit_3 : OS_TaskIdle_entail_wit_3.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_1 : OS_TaskIdle_partial_solve_wit_1.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_2_pure : OS_TaskIdle_partial_solve_wit_2_pure.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_2 : OS_TaskIdle_partial_solve_wit_2.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_3_pure : OS_TaskIdle_partial_solve_wit_3_pure.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_3 : OS_TaskIdle_partial_solve_wit_3.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_4 : OS_TaskIdle_partial_solve_wit_4.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_5 : OS_TaskIdle_partial_solve_wit_5.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_6_pure : OS_TaskIdle_partial_solve_wit_6_pure.
Axiom proof_of_OS_TaskIdle_partial_solve_wit_6 : OS_TaskIdle_partial_solve_wit_6.
Axiom proof_of_OS_TaskIdle_which_implies_wit_1 : OS_TaskIdle_which_implies_wit_1.
Axiom proof_of_OS_TaskIdle_which_implies_wit_2 : OS_TaskIdle_which_implies_wit_2.
Axiom proof_of_OS_TaskIdle_which_implies_wit_3 : OS_TaskIdle_which_implies_wit_3.

End VC_Correct.
