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
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_get_flags_rdy_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSFlagPendGetFlagsRdy -----*)

Definition OSFlagPendGetFlagsRdy_safety_wit_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH4 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  (caller )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagPendGetFlagsRdy_safety_wit_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH4 : (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot )) (PreH5 : (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual )) (PreH6 : ((task_reg_get_current_pointer (sg) (entry_2)) <> 0)) (PreH7 : (0 <= snapshot)) (PreH8 : (snapshot <= 65535)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH12 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  ((( &( "flags" ) )) # UShort  |-> snapshot)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (caller )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagPendGetFlagsRdy_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH4 : (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot )) (PreH5 : (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual )) (PreH6 : ((task_reg_get_current_pointer (sg) (entry_2)) <> 0)) (PreH7 : (0 <= snapshot)) (PreH8 : (snapshot <= 65535)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH12 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  (caller )
|--
  (flag_pend_get_flags_rdy_api_post platform critical sg invocation origin mask before caller snapshot X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH4 : (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot )) (PreH5 : (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual )) (PreH6 : ((task_reg_get_current_pointer (sg) (entry_2)) <> 0)) (PreH7 : (0 <= snapshot)) (PreH8 : (snapshot <= 65535)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH12 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  (caller )
|--
  (flag_pend_get_flags_rdy_api_post platform critical sg invocation origin mask before caller snapshot X )
).

Definition OSFlagPendGetFlagsRdy_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH4 : (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot )) (PreH5 : (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual )) (PreH6 : ((task_reg_get_current_pointer (sg) (entry_2)) <> 0)) (PreH7 : (0 <= snapshot)) (PreH8 : (snapshot <= 65535)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH12 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (time_get_restore_post platform critical sg invocation origin retval entry_2 )
  **  (caller )
|--
  (flag_pend_get_flags_rdy_api_post platform critical sg invocation origin mask before caller snapshot X )
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH3 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (flag_pend_get_flags_rdy_admission critical sg invocation before caller ) ” 
  &&  “ (flag_pend_get_flags_rdy_safe critical sg invocation before caller X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller )
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_2_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH4 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "flags" ) )) # UShort  |->_)
  **  (caller )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (flag_pend_get_flags_rdy_admission critical sg invocation before caller ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ”
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_2_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH4 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (flag_pend_get_flags_rdy_admission critical sg invocation before caller ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (flag_pend_get_flags_rdy_admission critical sg invocation before caller ) ” 
  &&  “ (flag_pend_get_flags_rdy_safe critical sg invocation before caller X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_2 := OSFlagPendGetFlagsRdy_partial_solve_wit_2_pure -> OSFlagPendGetFlagsRdy_partial_solve_wit_2_aux.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_3_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : (flag_pend_get_flags_rdy_observation sg caller entry snapshot )) (PreH4 : (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual )) (PreH5 : ((task_reg_get_current_pointer (sg) (entry)) <> 0)) (PreH6 : (0 <= snapshot)) (PreH7 : (snapshot <= 65535)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH10 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH11 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
  **  ((( &( "flags" ) )) # UShort  |-> snapshot)
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual ) ”
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_3_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH3 : (flag_pend_get_flags_rdy_observation sg caller entry snapshot )) (PreH4 : (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual )) (PreH5 : ((task_reg_get_current_pointer (sg) (entry)) <> 0)) (PreH6 : (0 <= snapshot)) (PreH7 : (snapshot <= 65535)) (PreH8 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH9 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH10 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH11 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (flag_pend_get_flags_rdy_observation sg caller entry snapshot ) ” 
  &&  “ (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual ) ” 
  &&  “ ((task_reg_get_current_pointer (sg) (entry)) <> 0) ” 
  &&  “ (0 <= snapshot) ” 
  &&  “ (snapshot <= 65535) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (flag_pend_get_flags_rdy_admission critical sg invocation before caller ) ” 
  &&  “ (flag_pend_get_flags_rdy_safe critical sg invocation before caller X ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_3 := OSFlagPendGetFlagsRdy_partial_solve_wit_3_pure -> OSFlagPendGetFlagsRdy_partial_solve_wit_3_aux.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_4_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH4 : (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot )) (PreH5 : (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual )) (PreH6 : ((task_reg_get_current_pointer (sg) (entry_2)) <> 0)) (PreH7 : (0 <= snapshot)) (PreH8 : (snapshot <= 65535)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH12 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  ((( &( "flags" ) )) # UShort  |-> snapshot)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
|--
  “ (retval = retval) ”
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_4_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (PreH1 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (time_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH4 : (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot )) (PreH5 : (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual )) (PreH6 : ((task_reg_get_current_pointer (sg) (entry_2)) <> 0)) (PreH7 : (0 <= snapshot)) (PreH8 : (snapshot <= 65535)) (PreH9 : (time_get_acquire_facts critical sg invocation mask retval before entry )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH12 : (flag_pend_get_flags_rdy_safe critical sg invocation before caller X )) ,
  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
|--
  “ (retval = retval) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry_2 ) ” 
  &&  “ (flag_pend_get_flags_rdy_observation sg caller entry_2 snapshot ) ” 
  &&  “ (flag_pend_get_flags_rdy_word_view sg entry_2 caller (task_reg_get_current_pointer (sg) (entry_2)) snapshot residual ) ” 
  &&  “ ((task_reg_get_current_pointer (sg) (entry_2)) <> 0) ” 
  &&  “ (0 <= snapshot) ” 
  &&  “ (snapshot <= 65535) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (flag_pend_get_flags_rdy_admission critical sg invocation before caller ) ” 
  &&  “ (flag_pend_get_flags_rdy_safe critical sg invocation before caller X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
.

Definition OSFlagPendGetFlagsRdy_partial_solve_wit_4 := OSFlagPendGetFlagsRdy_partial_solve_wit_4_pure -> OSFlagPendGetFlagsRdy_partial_solve_wit_4_aux.

Definition OSFlagPendGetFlagsRdy_which_implies_wit_1 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH3 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (residual: Assertion)  (snapshot: Z)  (entry: UCOS2_Verify_State) ,
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_pend_get_flags_rdy_observation sg caller entry snapshot ) ” 
  &&  “ (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual ) ” 
  &&  “ ((task_reg_get_current_pointer (sg) (entry)) <> 0) ” 
  &&  “ (0 <= snapshot) ” 
  &&  “ (snapshot <= 65535) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (flag_pend_get_flags_rdy_admission critical sg invocation before caller )) (PreH3 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (residual: Assertion)  (snapshot: Z)  (entry: UCOS2_Verify_State) ,
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (flag_pend_get_flags_rdy_observation sg caller entry snapshot ) ” 
  &&  “ (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual ) ” 
  &&  “ ((task_reg_get_current_pointer (sg) (entry)) <> 0) ” 
  &&  “ (0 <= snapshot) ” 
  &&  “ (snapshot <= 65535) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
).

Definition OSFlagPendGetFlagsRdy_which_implies_wit_2 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
|--
  “ (time_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (UCOS2_inv sg entry )
  **  (caller )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
|--
  (UCOS2_inv sg entry )
  **  (caller )
).

Definition OSFlagPendGetFlagsRdy_which_implies_wit_2_split_goal_spatial := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (time_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (flag_pend_get_flags_rdy_word_view sg entry caller (task_reg_get_current_pointer (sg) (entry)) snapshot residual )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((&(((task_reg_get_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> snapshot)
  **  (flag_pend_get_flags_rdy_read_frame sg entry residual )
|--
  (UCOS2_inv sg entry )
  **  (caller )
.

Module Type VC_Correct.


Axiom proof_of_OSFlagPendGetFlagsRdy_safety_wit_1 : OSFlagPendGetFlagsRdy_safety_wit_1.
Axiom proof_of_OSFlagPendGetFlagsRdy_safety_wit_2 : OSFlagPendGetFlagsRdy_safety_wit_2.
Axiom proof_of_OSFlagPendGetFlagsRdy_return_wit_1 : OSFlagPendGetFlagsRdy_return_wit_1.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_1 : OSFlagPendGetFlagsRdy_partial_solve_wit_1.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_2_pure : OSFlagPendGetFlagsRdy_partial_solve_wit_2_pure.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_2 : OSFlagPendGetFlagsRdy_partial_solve_wit_2.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_3_pure : OSFlagPendGetFlagsRdy_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_3 : OSFlagPendGetFlagsRdy_partial_solve_wit_3.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_4_pure : OSFlagPendGetFlagsRdy_partial_solve_wit_4_pure.
Axiom proof_of_OSFlagPendGetFlagsRdy_partial_solve_wit_4 : OSFlagPendGetFlagsRdy_partial_solve_wit_4.
Axiom proof_of_OSFlagPendGetFlagsRdy_which_implies_wit_1 : OSFlagPendGetFlagsRdy_which_implies_wit_1.
Axiom proof_of_OSFlagPendGetFlagsRdy_which_implies_wit_2 : OSFlagPendGetFlagsRdy_which_implies_wit_2.

End VC_Correct.
