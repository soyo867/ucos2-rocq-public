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
Require Import Ucos2Verify.VC.code.core.spec.stat_init_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSStatInit -----*)

Definition OSStatInit_safety_wit_1 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (retval: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X )) (PreH5 : (cpu_sr = 0)) ,
  (task_suspend_save_history_post environment critical saved_local sg delayed1 mask retval after_delay1 )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSStatInit_safety_wit_2 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active1 cpu_sr (stat_init_update (false) (acquired1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSStatInit_safety_wit_3 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) (PreH2 : (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (10 <> 0) ”
.

Definition OSStatInit_safety_wit_4 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (retval: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X )) ,
  (task_suspend_save_history_post environment critical saved_local sg delayed2 mask retval after_delay2 )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSStatInit_safety_wit_5 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active2 cpu_sr (stat_init_update (true) (acquired2)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSStatInit_entail_wit_1 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) (PreH2 : (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (time_dly_call_post environment critical saved_local sg original mask 2 initial frame (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) )
|--
  EX (delayed1: TaskSuspendCaller)  (after_delay1: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X ) ” 
  &&  “ (0 = 0) ”
  &&  (task_suspend_closed environment critical saved_local sg delayed1 mask after_delay1 )
  **  (frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) (PreH2 : (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (time_dly_call_post environment critical saved_local sg original mask 2 initial frame (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) )
|--
  EX (delayed1: TaskSuspendCaller)  (after_delay1: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg delayed1 mask after_delay1 )
  **  (frame )
).

Definition OSStatInit_entail_wit_2 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (retval: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X )) (PreH5 : (cpu_sr = 0)) ,
  (task_suspend_save_history_post environment critical saved_local sg delayed1 mask retval after_delay1 )
  **  (frame )
|--
  EX (active1: TaskSuspendCaller)  (acquired1: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 retval acquired1 X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired1)))))
  **  (stat_init_reset_residual sg (StatsState (acquired1)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active1 retval acquired1 )
  **  (frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (retval: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X )) (PreH5 : (cpu_sr = 0)) ,
  (task_suspend_save_history_post environment critical saved_local sg delayed1 mask retval after_delay1 )
  **  (frame )
|--
  EX (active1: TaskSuspendCaller)  (acquired1: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 retval acquired1 X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired1)))))
  **  (stat_init_reset_residual sg (StatsState (acquired1)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active1 retval acquired1 )
  **  (frame )
).

Definition OSStatInit_entail_wit_3 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (cpu_sr: Z) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  (stat_init_reset_residual sg (StatsState (acquired1)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active1 cpu_sr acquired1 )
  **  (frame )
|--
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X ) ”
  &&  (task_suspend_masked environment critical saved_local sg active1 cpu_sr acquired1 (stat_init_update (false) (acquired1)) )
  **  (frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (cpu_sr: Z) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  (stat_init_reset_residual sg (StatsState (acquired1)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active1 cpu_sr acquired1 )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg active1 cpu_sr acquired1 (stat_init_update (false) (acquired1)) )
  **  (frame )
).

Definition OSStatInit_entail_wit_3_split_goal_spatial := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (cpu_sr: Z) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  (stat_init_reset_residual sg (StatsState (acquired1)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active1 cpu_sr acquired1 )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg active1 cpu_sr acquired1 (stat_init_update (false) (acquired1)) )
  **  (frame )
.

Definition OSStatInit_entail_wit_4 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active1 cpu_sr (stat_init_update (false) (acquired1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  EX (caller2: TaskSuspendCaller)  (before2: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active1 cpu_sr (stat_init_update (false) (acquired1)) )
  **  (frame )
|--
  EX (caller2: TaskSuspendCaller)  (before2: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
).

Definition OSStatInit_entail_wit_5 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) (PreH2 : (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (time_dly_call_post environment critical saved_local sg caller2 mask 10 before2 frame (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )
|--
  EX (delayed2: TaskSuspendCaller)  (after_delay2: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg delayed2 mask after_delay2 )
  **  (frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) (PreH2 : (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (time_dly_call_post environment critical saved_local sg caller2 mask 10 before2 frame (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )
|--
  EX (delayed2: TaskSuspendCaller)  (after_delay2: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg delayed2 mask after_delay2 )
  **  (frame )
).

Definition OSStatInit_entail_wit_6 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (retval: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X )) ,
  (task_suspend_save_history_post environment critical saved_local sg delayed2 mask retval after_delay2 )
  **  (frame )
|--
  EX (active2: TaskSuspendCaller)  (acquired2: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 retval acquired2 X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (idleCtrMax ((StatsState (acquired2)))))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (stat_init_ready_byte ((StatsState (acquired2)))))
  **  (stat_init_calibration_residual sg (StatsState (acquired2)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active2 retval acquired2 )
  **  (frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (retval: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X )) ,
  (task_suspend_save_history_post environment critical saved_local sg delayed2 mask retval after_delay2 )
  **  (frame )
|--
  EX (active2: TaskSuspendCaller)  (acquired2: UCOS2_Verify_State) ,
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 retval acquired2 X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (idleCtrMax ((StatsState (acquired2)))))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (stat_init_ready_byte ((StatsState (acquired2)))))
  **  (stat_init_calibration_residual sg (StatsState (acquired2)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active2 retval acquired2 )
  **  (frame )
).

Definition OSStatInit_entail_wit_7 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (cpu_sr: Z) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> 1)
  **  (stat_init_calibration_residual sg (StatsState (acquired2)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active2 cpu_sr acquired2 )
  **  (frame )
|--
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X ) ”
  &&  (task_suspend_masked environment critical saved_local sg active2 cpu_sr acquired2 (stat_init_update (true) (acquired2)) )
  **  (frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (cpu_sr: Z) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (PreH1 : ((idleCtr ((StatsState (acquired2)))) <= UINT_MAX)) (PreH2 : ((idleCtr ((StatsState (acquired2)))) >= 0)) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> 1)
  **  (stat_init_calibration_residual sg (StatsState (acquired2)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active2 cpu_sr acquired2 )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg active2 cpu_sr acquired2 (stat_init_update (true) (acquired2)) )
  **  (frame )
).

Definition OSStatInit_entail_wit_7_split_goal_spatial := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (cpu_sr: Z) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (PreH1 : ((idleCtr ((StatsState (acquired2)))) <= UINT_MAX)) (PreH2 : ((idleCtr ((StatsState (acquired2)))) >= 0)) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (idleCtr ((StatsState (acquired2)))))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> 1)
  **  (stat_init_calibration_residual sg (StatsState (acquired2)) )
  **  (stat_init_statistics_frame environment critical saved_local sg active2 cpu_sr acquired2 )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg active2 cpu_sr acquired2 (stat_init_update (true) (acquired2)) )
  **  (frame )
.

Definition OSStatInit_entail_wit_8 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active2 cpu_sr (stat_init_update (true) (acquired2)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  (stat_init_call_post environment critical saved_local sg original mask initial frame X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active2 cpu_sr (stat_init_update (true) (acquired2)) )
  **  (frame )
|--
  (stat_init_call_post environment critical saved_local sg original mask initial frame X )
).

Definition OSStatInit_entail_wit_8_split_goal_spatial := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active2 cpu_sr (stat_init_update (true) (acquired2)) )
  **  (frame )
|--
  (stat_init_call_post environment critical saved_local sg original mask initial frame X )
.

Definition OSStatInit_return_wit_1 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) ,
  (stat_init_call_post environment critical saved_local sg original mask initial frame X )
|--
  (stat_init_call_post environment critical saved_local sg original mask initial frame X )
.

Definition OSStatInit_partial_solve_wit_1_pure := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
|--
  “ (stat_init_phase_facts environment critical sg original mask initial false original initial X ) ”
.

Definition OSStatInit_partial_solve_wit_1_aux := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
|--
  “ (stat_init_phase_facts environment critical sg original mask initial false original initial X ) ” 
  &&  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial false original initial X ) ”
  &&  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
.

Definition OSStatInit_partial_solve_wit_1 := OSStatInit_partial_solve_wit_1_pure -> OSStatInit_partial_solve_wit_1_aux.

Definition OSStatInit_partial_solve_wit_2_pure := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) (PreH2 : (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (time_dly_call_pre environment critical saved_local sg original mask 2 initial frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (2 = 2) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) ) ”
.

Definition OSStatInit_partial_solve_wit_2_aux := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) (PreH2 : (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (time_dly_call_pre environment critical saved_local sg original mask 2 initial frame )
|--
  “ (2 = 2) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial false original initial X ) ” 
  &&  “ (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) ) ” 
  &&  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial false original initial X ) ”
  &&  (time_dly_call_pre environment critical saved_local sg original mask 2 initial frame )
.

Definition OSStatInit_partial_solve_wit_2 := OSStatInit_partial_solve_wit_2_pure -> OSStatInit_partial_solve_wit_2_aux.

Definition OSStatInit_partial_solve_wit_3 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X )) (PreH5 : (cpu_sr = 0)) ,
  (task_suspend_closed environment critical saved_local sg delayed1 mask after_delay1 )
  **  (frame )
|--
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_delayed_facts environment critical sg original mask initial false original initial delayed1 after_delay1 X ) ” 
  &&  “ (cpu_sr = 0) ”
  &&  (task_suspend_closed environment critical saved_local sg delayed1 mask after_delay1 )
  **  (frame )
.

Definition OSStatInit_partial_solve_wit_4_pure := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_masked environment critical saved_local sg active1 cpu_sr acquired1 (stat_init_update (false) (acquired1)) )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSStatInit_partial_solve_wit_4_aux := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (delayed1: TaskSuspendCaller) (after_delay1: UCOS2_Verify_State) (active1: TaskSuspendCaller) (acquired1: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X )) ,
  (task_suspend_masked environment critical saved_local sg active1 cpu_sr acquired1 (stat_init_update (false) (acquired1)) )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial false original initial delayed1 after_delay1 active1 cpu_sr acquired1 X ) ”
  &&  (task_suspend_masked environment critical saved_local sg active1 cpu_sr acquired1 (stat_init_update (false) (acquired1)) )
  **  (frame )
.

Definition OSStatInit_partial_solve_wit_4 := OSStatInit_partial_solve_wit_4_pure -> OSStatInit_partial_solve_wit_4_aux.

Definition OSStatInit_partial_solve_wit_5_pure := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ”
.

Definition OSStatInit_partial_solve_wit_5_aux := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
|--
  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ” 
  &&  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
.

Definition OSStatInit_partial_solve_wit_5 := OSStatInit_partial_solve_wit_5_pure -> OSStatInit_partial_solve_wit_5_aux.

Definition OSStatInit_partial_solve_wit_6_pure := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) (PreH2 : (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((100 ÷ 10 ) = 10) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) ) ”
.

Definition OSStatInit_partial_solve_wit_6_aux := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) (PreH2 : (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) )) (PreH3 : (stat_init_config sg )) (PreH4 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
|--
  “ ((100 ÷ 10 ) = 10) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ” 
  &&  “ (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) ) ” 
  &&  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ”
  &&  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
.

Definition OSStatInit_partial_solve_wit_6 := OSStatInit_partial_solve_wit_6_pure -> OSStatInit_partial_solve_wit_6_aux.

Definition OSStatInit_partial_solve_wit_7 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X )) ,
  (task_suspend_closed environment critical saved_local sg delayed2 mask after_delay2 )
  **  (frame )
|--
  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_delayed_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 X ) ”
  &&  (task_suspend_closed environment critical saved_local sg delayed2 mask after_delay2 )
  **  (frame )
.

Definition OSStatInit_partial_solve_wit_8_pure := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_masked environment critical saved_local sg active2 cpu_sr acquired2 (stat_init_update (true) (acquired2)) )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSStatInit_partial_solve_wit_8_aux := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (delayed2: TaskSuspendCaller) (after_delay2: UCOS2_Verify_State) (active2: TaskSuspendCaller) (acquired2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (stat_init_config sg )) (PreH2 : (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X )) ,
  (task_suspend_masked environment critical saved_local sg active2 cpu_sr acquired2 (stat_init_update (true) (acquired2)) )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (stat_init_config sg ) ” 
  &&  “ (stat_init_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (stat_init_acquired_facts environment critical sg original mask initial true caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 X ) ”
  &&  (task_suspend_masked environment critical saved_local sg active2 cpu_sr acquired2 (stat_init_update (true) (acquired2)) )
  **  (frame )
.

Definition OSStatInit_partial_solve_wit_8 := OSStatInit_partial_solve_wit_8_pure -> OSStatInit_partial_solve_wit_8_aux.

Definition OSStatInit_which_implies_wit_1 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
|--
  “ (stat_init_phase_facts environment critical sg original mask initial false original initial X ) ” 
  &&  “ (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg original mask 2 initial frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
|--
  “ (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg original mask 2 initial frame )
).

Definition OSStatInit_which_implies_wit_1_split_goal_1 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
|--
  “ (time_dly_safe environment critical sg original mask 2 initial (stat_init_delay_continuation (environment) (critical) (sg) (original) (mask) (false) (initial) (X)) ) ”
.

Definition OSStatInit_which_implies_wit_1_split_goal_spatial := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial false original initial X )) ,
  (task_suspend_closed environment critical saved_local sg original mask initial )
  **  (frame )
|--
  (time_dly_call_pre environment critical saved_local sg original mask 2 initial frame )
.

Definition OSStatInit_which_implies_wit_2 := 
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
|--
  “ (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X ) ” 
  &&  “ (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
) \/
(
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
|--
  “ (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
).

Definition OSStatInit_which_implies_wit_2_split_goal_1 := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
|--
  “ (time_dly_safe environment critical sg caller2 mask 10 before2 (stat_init_delay_continuation (environment) (critical) (sg) (caller2) (mask) (true) (before2) (X)) ) ”
.

Definition OSStatInit_which_implies_wit_2_split_goal_spatial := 
forall (frame: Assertion) (initial: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller2: TaskSuspendCaller) (before2: UCOS2_Verify_State) (PreH1 : (stat_init_phase_facts environment critical sg original mask initial true caller2 before2 X )) ,
  (task_suspend_closed environment critical saved_local sg caller2 mask before2 )
  **  (frame )
|--
  (time_dly_call_pre environment critical saved_local sg caller2 mask 10 before2 frame )
.

Module Type VC_Correct.


Axiom proof_of_OSStatInit_safety_wit_1 : OSStatInit_safety_wit_1.
Axiom proof_of_OSStatInit_safety_wit_2 : OSStatInit_safety_wit_2.
Axiom proof_of_OSStatInit_safety_wit_3 : OSStatInit_safety_wit_3.
Axiom proof_of_OSStatInit_safety_wit_4 : OSStatInit_safety_wit_4.
Axiom proof_of_OSStatInit_safety_wit_5 : OSStatInit_safety_wit_5.
Axiom proof_of_OSStatInit_entail_wit_1 : OSStatInit_entail_wit_1.
Axiom proof_of_OSStatInit_entail_wit_2 : OSStatInit_entail_wit_2.
Axiom proof_of_OSStatInit_entail_wit_3 : OSStatInit_entail_wit_3.
Axiom proof_of_OSStatInit_entail_wit_4 : OSStatInit_entail_wit_4.
Axiom proof_of_OSStatInit_entail_wit_5 : OSStatInit_entail_wit_5.
Axiom proof_of_OSStatInit_entail_wit_6 : OSStatInit_entail_wit_6.
Axiom proof_of_OSStatInit_entail_wit_7 : OSStatInit_entail_wit_7.
Axiom proof_of_OSStatInit_entail_wit_8 : OSStatInit_entail_wit_8.
Axiom proof_of_OSStatInit_return_wit_1 : OSStatInit_return_wit_1.
Axiom proof_of_OSStatInit_partial_solve_wit_1_pure : OSStatInit_partial_solve_wit_1_pure.
Axiom proof_of_OSStatInit_partial_solve_wit_1 : OSStatInit_partial_solve_wit_1.
Axiom proof_of_OSStatInit_partial_solve_wit_2_pure : OSStatInit_partial_solve_wit_2_pure.
Axiom proof_of_OSStatInit_partial_solve_wit_2 : OSStatInit_partial_solve_wit_2.
Axiom proof_of_OSStatInit_partial_solve_wit_3 : OSStatInit_partial_solve_wit_3.
Axiom proof_of_OSStatInit_partial_solve_wit_4_pure : OSStatInit_partial_solve_wit_4_pure.
Axiom proof_of_OSStatInit_partial_solve_wit_4 : OSStatInit_partial_solve_wit_4.
Axiom proof_of_OSStatInit_partial_solve_wit_5_pure : OSStatInit_partial_solve_wit_5_pure.
Axiom proof_of_OSStatInit_partial_solve_wit_5 : OSStatInit_partial_solve_wit_5.
Axiom proof_of_OSStatInit_partial_solve_wit_6_pure : OSStatInit_partial_solve_wit_6_pure.
Axiom proof_of_OSStatInit_partial_solve_wit_6 : OSStatInit_partial_solve_wit_6.
Axiom proof_of_OSStatInit_partial_solve_wit_7 : OSStatInit_partial_solve_wit_7.
Axiom proof_of_OSStatInit_partial_solve_wit_8_pure : OSStatInit_partial_solve_wit_8_pure.
Axiom proof_of_OSStatInit_partial_solve_wit_8 : OSStatInit_partial_solve_wit_8.
Axiom proof_of_OSStatInit_which_implies_wit_1 : OSStatInit_which_implies_wit_1.
Axiom proof_of_OSStatInit_which_implies_wit_2 : OSStatInit_which_implies_wit_2.

End VC_Correct.
