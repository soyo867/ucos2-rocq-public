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
Require Import Ucos2Verify.VC.code.task.spec.task_return_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_TaskReturn -----*)

Definition OS_TaskReturn_return_wit_1 := 
(
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_post environment critical saved_local sg 255 (LitMap (("?"%string))) call mask initial retval )
  **  (GlobalStrings LitMap )
|--
  (task_return_post environment critical saved_local sg (LitMap (("?"%string))) call mask initial )
  **  (GlobalStrings LitMap )
) \/
(
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_post environment critical saved_local sg 255 (LitMap (("?"%string))) call mask initial retval )
  **  (GlobalStrings LitMap )
|--
  (task_return_post environment critical saved_local sg (LitMap (("?"%string))) call mask initial )
  **  (GlobalStrings LitMap )
).

Definition OS_TaskReturn_return_wit_1_split_goal_spatial := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_post environment critical saved_local sg 255 (LitMap (("?"%string))) call mask initial retval )
  **  (GlobalStrings LitMap )
|--
  (task_return_post environment critical saved_local sg (LitMap (("?"%string))) call mask initial )
  **  (GlobalStrings LitMap )
.

Definition OS_TaskReturn_partial_solve_wit_1_pure := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
  **  (GlobalStrings LitMap )
|--
  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ”
.

Definition OS_TaskReturn_partial_solve_wit_1_aux := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
  **  (GlobalStrings LitMap )
|--
  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
  **  (GlobalStrings LitMap )
.

Definition OS_TaskReturn_partial_solve_wit_1 := OS_TaskReturn_partial_solve_wit_1_pure -> OS_TaskReturn_partial_solve_wit_1_aux.

Definition OS_TaskReturn_partial_solve_wit_2 := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
  **  (GlobalStrings LitMap )
|--
  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (GlobalStrings LitMap )
.

Definition OS_TaskReturn_partial_solve_wit_3 := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (GlobalStrings LitMap )
|--
  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
  **  (GlobalStrings LitMap )
.

Definition OS_TaskReturn_partial_solve_wit_4_pure := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
  **  (GlobalStrings LitMap )
|--
  “ (255 = 255) ” 
  &&  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
.

Definition OS_TaskReturn_partial_solve_wit_4_aux := 
forall (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
  **  (GlobalStrings LitMap )
|--
  “ (255 = 255) ” 
  &&  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
  **  (GlobalStrings LitMap )
.

Definition OS_TaskReturn_partial_solve_wit_4 := OS_TaskReturn_partial_solve_wit_4_pure -> OS_TaskReturn_partial_solve_wit_4_aux.

Definition OS_TaskReturn_which_implies_wit_1 := 
(
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
|--
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
) \/
(
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
|--
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
).

Definition OS_TaskReturn_which_implies_wit_1_split_goal_spatial := 
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_delete_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTaskCtr" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSRunning" ) ) )) ,
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
|--
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
.

Definition OS_TaskReturn_which_implies_wit_2 := 
(
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
|--
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
) \/
(
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
|--
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
).

Definition OS_TaskReturn_which_implies_wit_2_split_goal_spatial := 
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (completed: TaskDeleteCompletedEnvironment) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_delete_current (sg) (initial)))
  **  (wand (task_delete_ptr_cell (( &( "OSTCBCur" ) )) ((task_delete_current (sg) (initial)))) (task_delete_entry (environment) (critical) (saved_local) (completed) (sg) (255) (call) (mask) (initial)) )
|--
  (task_delete_entry environment critical saved_local completed sg 255 call mask initial )
.

Module Type VC_Correct.


Axiom proof_of_OS_TaskReturn_return_wit_1 : OS_TaskReturn_return_wit_1.
Axiom proof_of_OS_TaskReturn_partial_solve_wit_1_pure : OS_TaskReturn_partial_solve_wit_1_pure.
Axiom proof_of_OS_TaskReturn_partial_solve_wit_1 : OS_TaskReturn_partial_solve_wit_1.
Axiom proof_of_OS_TaskReturn_partial_solve_wit_2 : OS_TaskReturn_partial_solve_wit_2.
Axiom proof_of_OS_TaskReturn_partial_solve_wit_3 : OS_TaskReturn_partial_solve_wit_3.
Axiom proof_of_OS_TaskReturn_partial_solve_wit_4_pure : OS_TaskReturn_partial_solve_wit_4_pure.
Axiom proof_of_OS_TaskReturn_partial_solve_wit_4 : OS_TaskReturn_partial_solve_wit_4.
Axiom proof_of_OS_TaskReturn_which_implies_wit_1 : OS_TaskReturn_which_implies_wit_1.
Axiom proof_of_OS_TaskReturn_which_implies_wit_2 : OS_TaskReturn_which_implies_wit_2.

End VC_Correct.
