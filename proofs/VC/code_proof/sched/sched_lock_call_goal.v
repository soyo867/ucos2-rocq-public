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
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_call_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSSchedLock -----*)

Definition OSSchedLock_safety_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (os_sched_lock_body_facts critical sg invocation mask retval before entry )) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedLock_safety_wit_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_post platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSchedLock_entail_wit_1_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_lock_locks (entry_3)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) = 0)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH5 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH6 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH10 : (os_sched_lock_continuation critical sg invocation before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry_3 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry_3)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((os_sched_lock_locks (entry_3)) + 1 ))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_3 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_lock_locks (entry_3)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) = 0)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH5 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH6 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH10 : (os_sched_lock_continuation critical sg invocation before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  TT && emp 
|--
  “ (((os_sched_lock_locks (entry_3)) + 1 ) = (os_sched_lock_updated_locks (entry_3))) ”
  &&  emp
).

Definition OSSchedLock_entail_wit_1_1_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_lock_locks (entry_3)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) = 0)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH5 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH6 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH10 : (os_sched_lock_continuation critical sg invocation before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (((os_sched_lock_locks (entry_3)) + 1 ) = (os_sched_lock_updated_locks (entry_3)))
.

Definition OSSchedLock_entail_wit_1_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_lock_locks (entry_3)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) = 0)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH5 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH6 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH10 : (os_sched_lock_continuation critical sg invocation before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry_3 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry_3)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_locks (entry_3)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_3 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_lock_locks (entry_3)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) = 0)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH5 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH6 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH10 : (os_sched_lock_continuation critical sg invocation before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  TT && emp 
|--
  “ ((os_sched_lock_locks (entry_3)) = (os_sched_lock_updated_locks (entry_3))) ”
  &&  emp
).

Definition OSSchedLock_entail_wit_1_2_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((os_sched_lock_locks (entry_3)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) = 0)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH5 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH6 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH9 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH10 : (os_sched_lock_continuation critical sg invocation before X )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((os_sched_lock_locks (entry_3)) = (os_sched_lock_updated_locks (entry_3)))
.

Definition OSSchedLock_entail_wit_1_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) <> 0)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH5 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH8 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH9 : (os_sched_lock_continuation critical sg invocation before X )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry_3 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry_3)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_locks (entry_3)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_3 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) <> 0)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH5 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH8 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH9 : (os_sched_lock_continuation critical sg invocation before X )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  TT && emp 
|--
  “ ((os_sched_lock_locks (entry_3)) = (os_sched_lock_updated_locks (entry_3))) ”
  &&  emp
).

Definition OSSchedLock_entail_wit_1_3_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (entry_3: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_ints (entry_3))) (32)) <> 0)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_3 )) (PreH4 : (0 <= (os_sched_lock_locks (entry_3)))) (PreH5 : ((os_sched_lock_locks (entry_3)) <= 255)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (os_sched_lock_body_facts critical sg invocation mask retval before entry_2 )) (PreH8 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH9 : (os_sched_lock_continuation critical sg invocation before X )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((os_sched_lock_locks (entry_3)) = (os_sched_lock_updated_locks (entry_3)))
.

Definition OSSchedLock_return_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_post platform critical sg invocation origin mask before )
|--
  (os_sched_lock_program_post platform critical sg invocation origin mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_post platform critical sg invocation origin mask before )
|--
  (os_sched_lock_program_post platform critical sg invocation origin mask before X )
).

Definition OSSchedLock_return_wit_1_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (entry_2: UCOS2_Verify_State) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_post platform critical sg invocation origin mask before )
|--
  (os_sched_lock_program_post platform critical sg invocation origin mask before X )
.

Definition OSSchedLock_return_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) <> 1)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
|--
  (os_sched_lock_program_post platform critical sg invocation origin mask before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) <> 1)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
|--
  (os_sched_lock_program_post platform critical sg invocation origin mask before X )
).

Definition OSSchedLock_return_wit_2_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) <> 1)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
|--
  (os_sched_lock_program_post platform critical sg invocation origin mask before X )
.

Definition OSSchedLock_partial_solve_wit_1_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSSchedLock_partial_solve_wit_1_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
.

Definition OSSchedLock_partial_solve_wit_1 := OSSchedLock_partial_solve_wit_1_pure -> OSSchedLock_partial_solve_wit_1_aux.

Definition OSSchedLock_partial_solve_wit_2_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_lock_running (before)) = 1) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH4 : (os_sched_lock_continuation critical sg invocation before X )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ ((os_sched_lock_running (before)) = 1) ”
).

Definition OSSchedLock_partial_solve_wit_2_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH4 : (os_sched_lock_continuation critical sg invocation before X )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ ((os_sched_lock_running (before)) = 1) ”
.

Definition OSSchedLock_partial_solve_wit_2_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH2 : (os_sched_lock_continuation critical sg invocation before X )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_lock_running (before)) = 1) ” 
  &&  “ ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1) ” 
  &&  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
.

Definition OSSchedLock_partial_solve_wit_2 := OSSchedLock_partial_solve_wit_2_pure -> OSSchedLock_partial_solve_wit_2_aux.

Definition OSSchedLock_partial_solve_wit_3_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (os_sched_lock_body_facts critical sg invocation mask retval before entry )) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSSchedLock_partial_solve_wit_3_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (os_sched_lock_body_facts critical sg invocation mask retval before entry )) (PreH2 : ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1)) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
|--
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask retval before entry ) ” 
  &&  “ ((unsigned_last_nbits ((os_sched_lock_running (before))) (32)) = 1) ” 
  &&  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
.

Definition OSSchedLock_partial_solve_wit_3 := OSSchedLock_partial_solve_wit_3_pure -> OSSchedLock_partial_solve_wit_3_aux.

Definition OSSchedLock_partial_solve_wit_4_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
|--
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSSchedLock_partial_solve_wit_4_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
|--
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
.

Definition OSSchedLock_partial_solve_wit_4 := OSSchedLock_partial_solve_wit_4_pure -> OSSchedLock_partial_solve_wit_4_aux.

Definition OSSchedLock_partial_solve_wit_5_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_lock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ”
.

Definition OSSchedLock_partial_solve_wit_5_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (os_sched_lock_continuation critical sg invocation before X )) (PreH4 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH5 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_lock_checkpoint (true) (entry)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_lock_checkpoint (true) (entry)) )
.

Definition OSSchedLock_partial_solve_wit_5 := OSSchedLock_partial_solve_wit_5_pure -> OSSchedLock_partial_solve_wit_5_aux.

Definition OSSchedLock_which_implies_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_continuation critical sg invocation before X ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
).

Definition OSSchedLock_which_implies_wit_1_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSSchedLock_which_implies_wit_1_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  “ (os_sched_lock_continuation critical sg invocation before X ) ”
.

Definition OSSchedLock_which_implies_wit_1_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_program_pre platform critical sg invocation origin mask before X )
|--
  ((( &( "OSRunning" ) )) # UChar  |-> (os_sched_lock_running (before)))
  **  (os_sched_lock_outside_frame platform critical sg invocation origin mask before )
.

Definition OSSchedLock_which_implies_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= (os_sched_lock_locks (entry))) ” 
  &&  “ ((os_sched_lock_locks (entry)) <= 255) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= (os_sched_lock_locks (entry))) ” 
  &&  “ ((os_sched_lock_locks (entry)) <= 255) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_locks (entry)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry )
).

Definition OSSchedLock_which_implies_wit_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_lock_checkpoint (true) (entry)) )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_lock_continuation critical sg invocation before X )) (PreH2 : (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH3 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_lock_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_lock_updated_locks (entry_2)))
  **  (UCOS2_raw_rep_missing_interrupt sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_lock_continuation critical sg invocation before X ) ” 
  &&  “ (os_sched_lock_body_facts critical sg invocation mask cpu_sr before entry ) ”
  &&  (os_sched_lock_inside_frame platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_lock_checkpoint (true) (entry)) )
).

Module Type VC_Correct.


Axiom proof_of_OSSchedLock_safety_wit_1 : OSSchedLock_safety_wit_1.
Axiom proof_of_OSSchedLock_safety_wit_2 : OSSchedLock_safety_wit_2.
Axiom proof_of_OSSchedLock_entail_wit_1_1 : OSSchedLock_entail_wit_1_1.
Axiom proof_of_OSSchedLock_entail_wit_1_2 : OSSchedLock_entail_wit_1_2.
Axiom proof_of_OSSchedLock_entail_wit_1_3 : OSSchedLock_entail_wit_1_3.
Axiom proof_of_OSSchedLock_return_wit_1 : OSSchedLock_return_wit_1.
Axiom proof_of_OSSchedLock_return_wit_2 : OSSchedLock_return_wit_2.
Axiom proof_of_OSSchedLock_partial_solve_wit_1_pure : OSSchedLock_partial_solve_wit_1_pure.
Axiom proof_of_OSSchedLock_partial_solve_wit_1 : OSSchedLock_partial_solve_wit_1.
Axiom proof_of_OSSchedLock_partial_solve_wit_2_pure : OSSchedLock_partial_solve_wit_2_pure.
Axiom proof_of_OSSchedLock_partial_solve_wit_2 : OSSchedLock_partial_solve_wit_2.
Axiom proof_of_OSSchedLock_partial_solve_wit_3_pure : OSSchedLock_partial_solve_wit_3_pure.
Axiom proof_of_OSSchedLock_partial_solve_wit_3 : OSSchedLock_partial_solve_wit_3.
Axiom proof_of_OSSchedLock_partial_solve_wit_4_pure : OSSchedLock_partial_solve_wit_4_pure.
Axiom proof_of_OSSchedLock_partial_solve_wit_4 : OSSchedLock_partial_solve_wit_4.
Axiom proof_of_OSSchedLock_partial_solve_wit_5_pure : OSSchedLock_partial_solve_wit_5_pure.
Axiom proof_of_OSSchedLock_partial_solve_wit_5 : OSSchedLock_partial_solve_wit_5.
Axiom proof_of_OSSchedLock_which_implies_wit_1 : OSSchedLock_which_implies_wit_1.
Axiom proof_of_OSSchedLock_which_implies_wit_2 : OSSchedLock_which_implies_wit_2.
Axiom proof_of_OSSchedLock_which_implies_wit_3 : OSSchedLock_which_implies_wit_3.

End VC_Correct.
