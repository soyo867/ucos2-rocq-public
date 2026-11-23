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
Require Import Ucos2Verify.VC.code.core.spec.task_stat_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_TaskStat -----*)

Definition OS_TaskStat_safety_wit_1 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (10 <> 0) ”
.

Definition OS_TaskStat_safety_wit_2 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (100 <> 0) ”
.

Definition OS_TaskStat_safety_wit_3 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((task_stat_maximum (zs)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  (task_suspend_save_history_post environment critical saved_local sg zc zm retval zs )
  **  (frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStat_safety_wit_4 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (cpu_sr: Z) (init_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg init_caller cpu_sr init_released )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStat_safety_wit_5 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_configuration sg )) (PreH6 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OS_TaskStat_safety_wit_6 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OS_TaskStat_safety_wit_7 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X )) (PreH2 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_save_history_post environment critical saved_local sg one_returned lm retval one_current )
  **  (frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStat_safety_wit_8 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (cpu_sr: Z) (reset_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg reset_caller cpu_sr reset_released )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStat_safety_wit_9 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (PreH1 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (10 <> 0) ”
.

Definition OS_TaskStat_safety_wit_10 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X )) (PreH2 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_save_history_post environment critical saved_local sg window_returned window_mask retval window_current )
  **  (frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStat_safety_wit_11 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (cpu_sr: Z) (idle_run: Z) (idle_max: Z) (capture_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) ,
  (task_suspend_restore_history_post environment critical saved_local sg capture_caller cpu_sr capture_released )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStat_safety_wit_12 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : (idle_max <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH9 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (sample_state)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (idle_max <> 0) ”
.

Definition OS_TaskStat_safety_wit_13 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (sample_caller: TaskSuspendCaller) (sample_mask: Z) (usage_written: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (idle_pct: Z) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH6 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH7 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH8 : (idle_pct = (idle_run ÷ idle_max ))) (PreH9 : (idle_pct > 100)) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRecalibrate ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) usage_written X )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  ((( &( "idle_pct" ) )) # UInt  |-> idle_pct)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (usage_written)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (usage_written)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (usage_written)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (usage_written)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (usage_written)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask usage_written )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (100 <> 0) ”
.

Definition OS_TaskStat_entail_wit_1 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH6 : (p_arg_pre = argument)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (before)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (before)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (before)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (before)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (before)))
  **  (task_stat_closed_statistics_frame environment saved_local sg original initial_mask before )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  EX (rc: TaskSuspendCaller)  (rm: Z)  (rs: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
.

Definition OS_TaskStat_entail_wit_2 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc_2: TaskSuspendCaller) (rm_2: Z) (rs_2: UCOS2_Verify_State) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (ready_returned) (rm_2)) ready_current X )) (PreH6 : (time_dly_safe environment critical sg rc_2 rm_2 20 rs_2 (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc_2) (rm_2) (20) (TaskStatReady) (rs_2) (X)) )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : ((unsigned_last_nbits ((task_stat_ready (rs_2))) (32)) = 0)) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc_2) (rm_2)) rs_2 X )) (PreH17 : (task_stat_configuration sg )) (PreH18 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH22 : (p_arg_pre = argument)) (PreH23 : (task_stat_configuration sg )) (PreH24 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH25 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (ready_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (ready_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (ready_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (ready_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (ready_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg ready_returned rm_2 ready_current )
  **  (frame )
|--
  EX (rc: TaskSuspendCaller)  (rm: Z)  (rs: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
.

Definition OS_TaskStat_entail_wit_3 := 
(
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (unsigned_last_nbits (((task_stat_maximum (rs)) ÷ 100 )) (32)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  EX (scaled_caller: TaskSuspendCaller)  (scaled_mask: Z)  (scaled: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (scaled)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (scaled)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (scaled)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (scaled)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (scaled)))
  **  (task_stat_closed_statistics_frame environment saved_local sg scaled_caller scaled_mask scaled )
  **  (frame )
) \/
(
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (rc) (rm)) rs X ) ” 
  &&  “ ((unsigned_last_nbits (((task_stat_maximum (rs)) ÷ 100 )) (32)) = (task_stat_maximum (rs))) ”
  &&  emp
).

Definition OS_TaskStat_entail_wit_3_split_goal_1 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (rc) (rm)) rs X )
.

Definition OS_TaskStat_entail_wit_3_split_goal_2 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((unsigned_last_nbits (((task_stat_maximum (rs)) ÷ 100 )) (32)) = (task_stat_maximum (rs)))
.

Definition OS_TaskStat_entail_wit_4 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (scaled)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (scaled)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (scaled)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (scaled)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (scaled)))
  **  (task_stat_closed_statistics_frame environment saved_local sg scaled_caller scaled_mask scaled )
  **  (frame )
|--
  EX (zc: TaskSuspendCaller)  (zm: Z)  (zs: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
.

Definition OS_TaskStat_entail_wit_5 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroUsage) (zc) (zm)) zs X )) (PreH6 : ((task_stat_maximum (zs)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  EX (zero_written: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (zs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (zs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (zs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (zs)) >= 0)) (PreH5 : ((task_stat_maximum (zs)) >= 0)) (PreH6 : ((task_stat_counter (zs)) >= 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroUsage) (zc) (zm)) zs X )) (PreH12 : ((task_stat_maximum (zs)) = 0)) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH22 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  EX (zero_written: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
).

Definition OS_TaskStat_entail_wit_6 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_refined_call_post environment critical saved_local sg zc zm zero_written 255 frame retval (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) )
|--
  EX (suspend_returned: TaskSuspendCaller)  (suspend_current: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (suspend_returned) (zm)) suspend_current X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (suspend_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (suspend_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (suspend_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (suspend_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (suspend_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg suspend_returned zm suspend_current )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_refined_call_post environment critical saved_local sg zc zm zero_written 255 frame retval (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) )
|--
  EX (suspend_returned: TaskSuspendCaller)  (suspend_current: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (suspend_returned) (zm)) suspend_current X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (suspend_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (suspend_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (suspend_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (suspend_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (suspend_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg suspend_returned zm suspend_current )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_7 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm_2: Z) (suspend_returned: TaskSuspendCaller) (suspend_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (suspend_returned) (zm_2)) suspend_current X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (suspend_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (suspend_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (suspend_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (suspend_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (suspend_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg suspend_returned zm_2 suspend_current )
  **  (frame )
|--
  EX (zc: TaskSuspendCaller)  (zm: Z)  (zs: UCOS2_Verify_State)  (scaled_caller: TaskSuspendCaller)  (scaled_mask: Z)  (scaled: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
.

Definition OS_TaskStat_entail_wit_8 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((task_stat_maximum (zs)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  (task_suspend_save_history_post environment critical saved_local sg zc zm retval zs )
  **  (frame )
|--
  EX (init_caller: TaskSuspendCaller)  (init_acquired: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatInitialize) (retval) (init_acquired))) (init_caller) (zm)) init_acquired X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (init_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (init_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (init_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (init_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (init_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg init_caller retval init_acquired init_acquired )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((task_stat_maximum (zs)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  (task_suspend_save_history_post environment critical saved_local sg zc zm retval zs )
  **  (frame )
|--
  EX (init_caller: TaskSuspendCaller)  (init_acquired: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatInitialize) (retval) (init_acquired))) (init_caller) (zm)) init_acquired X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (init_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (init_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (init_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (init_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (init_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg init_caller retval init_acquired init_acquired )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_9 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (cpu_sr: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatInitialize) (cpu_sr) (init_acquired))) (init_caller) (zm)) init_acquired X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (unsigned_last_nbits (((task_stat_maximum (init_acquired)) * 100 )) (32)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (init_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (init_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (init_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (init_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg init_caller cpu_sr init_acquired init_acquired )
  **  (frame )
|--
  EX (init_released: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X ) ”
  &&  (task_suspend_masked environment critical saved_local sg init_caller cpu_sr init_acquired init_released )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (cpu_sr: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (PreH1 : ((task_stat_run (init_acquired)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (init_acquired)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((task_stat_maximum (init_acquired)) * 100 )) (32)) <= UINT_MAX)) (PreH4 : ((task_stat_run (init_acquired)) >= 0)) (PreH5 : ((task_stat_maximum (init_acquired)) >= 0)) (PreH6 : ((unsigned_last_nbits (((task_stat_maximum (init_acquired)) * 100 )) (32)) >= 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatInitialize) (cpu_sr) (init_acquired))) (init_caller) (zm)) init_acquired X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (unsigned_last_nbits (((task_stat_maximum (init_acquired)) * 100 )) (32)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (init_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (init_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (init_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (init_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg init_caller cpu_sr init_acquired init_acquired )
  **  (frame )
|--
  EX (init_released: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X ) ”
  &&  (task_suspend_masked environment critical saved_local sg init_caller cpu_sr init_acquired init_released )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_10 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (cpu_sr: Z) (init_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg init_caller cpu_sr init_released )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  EX (initial_returned: TaskSuspendCaller)  (initial_after_mask: Z)  (initial_current: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick initial_returned initial_after_mask initial_current X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (cpu_sr: Z) (init_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg init_caller cpu_sr init_released )
  **  (frame )
|--
  EX (initial_returned: TaskSuspendCaller)  (initial_after_mask: Z)  (initial_current: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick initial_returned initial_after_mask initial_current X )
).

Definition OS_TaskStat_entail_wit_11 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (initial_returned: TaskSuspendCaller) (initial_current: UCOS2_Verify_State) (initial_after_mask: Z) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick initial_returned initial_after_mask initial_current X )
|--
  EX (lc: TaskSuspendCaller)  (lm: Z)  (ls: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
.

Definition OS_TaskStat_entail_wit_12 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X )) (PreH2 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_save_history_post environment critical saved_local sg one_returned lm retval one_current )
  **  (frame )
|--
  EX (reset_caller: TaskSuspendCaller)  (reset_acquired: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatReset) (retval) (reset_acquired))) (reset_caller) (lm)) reset_acquired X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (reset_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (reset_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (reset_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (reset_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (reset_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg reset_caller retval reset_acquired reset_acquired )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X )) (PreH2 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_save_history_post environment critical saved_local sg one_returned lm retval one_current )
  **  (frame )
|--
  EX (reset_caller: TaskSuspendCaller)  (reset_acquired: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatReset) (retval) (reset_acquired))) (reset_caller) (lm)) reset_acquired X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (reset_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (reset_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (reset_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (reset_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (reset_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg reset_caller retval reset_acquired reset_acquired )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_13 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (cpu_sr: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatReset) (cpu_sr) (reset_acquired))) (reset_caller) (lm)) reset_acquired X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (reset_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (reset_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (reset_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (reset_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_acquired )
  **  (frame )
|--
  EX (reset_released: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X ) ”
  &&  (task_suspend_masked environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_released )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (cpu_sr: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (PreH1 : ((task_stat_run (reset_acquired)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (reset_acquired)) <= UINT_MAX)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : ((task_stat_run (reset_acquired)) >= 0)) (PreH5 : ((task_stat_maximum (reset_acquired)) >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatReset) (cpu_sr) (reset_acquired))) (reset_caller) (lm)) reset_acquired X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (reset_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (reset_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (reset_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (reset_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_acquired )
  **  (frame )
|--
  EX (reset_released: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X ) ”
  &&  (task_suspend_masked environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_released )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_14 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (cpu_sr: Z) (reset_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg reset_caller cpu_sr reset_released )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  EX (window_caller: TaskSuspendCaller)  (window_mask: Z)  (window_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (cpu_sr: Z) (reset_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X )) ,
  (task_suspend_restore_history_post environment critical saved_local sg reset_caller cpu_sr reset_released )
  **  (frame )
|--
  EX (window_caller: TaskSuspendCaller)  (window_mask: Z)  (window_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
).

Definition OS_TaskStat_entail_wit_15 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X )) (PreH2 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_save_history_post environment critical saved_local sg window_returned window_mask retval window_current )
  **  (frame )
|--
  EX (capture_caller: TaskSuspendCaller)  (capture_acquired: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatCapture) (retval) (capture_acquired))) (capture_caller) (window_mask)) capture_acquired X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (capture_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (capture_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (capture_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (capture_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (capture_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg capture_caller retval capture_acquired capture_acquired )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X )) (PreH2 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_save_history_post environment critical saved_local sg window_returned window_mask retval window_current )
  **  (frame )
|--
  EX (capture_caller: TaskSuspendCaller)  (capture_acquired: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatCapture) (retval) (capture_acquired))) (capture_caller) (window_mask)) capture_acquired X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (capture_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (capture_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (capture_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (capture_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (capture_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg capture_caller retval capture_acquired capture_acquired )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_16 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (cpu_sr: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatCapture) (cpu_sr) (capture_acquired))) (capture_caller) (window_mask)) capture_acquired X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (capture_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (capture_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_counter (capture_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (capture_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (capture_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_acquired )
  **  (frame )
|--
  EX (capture_released: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X ) ” 
  &&  “ ((task_stat_counter (capture_acquired)) = (task_stat_counter (capture_acquired))) ” 
  &&  “ ((task_stat_maximum (capture_acquired)) = (task_stat_maximum (capture_acquired))) ” 
  &&  “ (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) ) ”
  &&  (task_suspend_masked environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_released )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (cpu_sr: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (capture_acquired)) <= UINT_MAX)) (PreH2 : ((task_stat_counter (capture_acquired)) <= UINT_MAX)) (PreH3 : ((task_stat_maximum (capture_acquired)) >= 0)) (PreH4 : ((task_stat_counter (capture_acquired)) >= 0)) (PreH5 : (task_stat_configuration sg )) (PreH6 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatProtected (TaskStatCapture) (cpu_sr) (capture_acquired))) (capture_caller) (window_mask)) capture_acquired X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (capture_acquired)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (capture_acquired)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_counter (capture_acquired)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (capture_acquired)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (capture_acquired)))
  **  (task_stat_masked_statistics_frame environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_acquired )
  **  (frame )
|--
  EX (capture_released: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X ) ” 
  &&  “ (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) ) ”
  &&  (task_suspend_masked environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_released )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_17 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (cpu_sr: Z) (idle_run: Z) (idle_max: Z) (capture_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) ,
  (task_suspend_restore_history_post environment critical saved_local sg capture_caller cpu_sr capture_released )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
|--
  EX (sample_caller: TaskSuspendCaller)  (sample_mask: Z)  (sample_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (idle_run = (task_stat_counter (capture_acquired))) ” 
  &&  “ (idle_max = (task_stat_maximum (capture_acquired))) ” 
  &&  “ (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (sample_state)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (cpu_sr: Z) (idle_run: Z) (idle_max: Z) (capture_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) ,
  (task_suspend_restore_history_post environment critical saved_local sg capture_caller cpu_sr capture_released )
  **  (frame )
|--
  EX (sample_caller: TaskSuspendCaller)  (sample_mask: Z)  (sample_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (idle_run = (task_stat_counter (capture_acquired))) ” 
  &&  “ (idle_max = (task_stat_maximum (capture_acquired))) ” 
  &&  “ (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (sample_state)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
).

Definition OS_TaskStat_entail_wit_18 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((idle_run ÷ idle_max ) > 100)) (PreH2 : (idle_max <> 0)) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH8 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH9 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
|--
  EX (usage_written: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (idle_run = (task_stat_counter (capture_acquired))) ” 
  &&  “ (idle_max = (task_stat_maximum (capture_acquired))) ” 
  &&  “ (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) ) ” 
  &&  “ ((idle_run ÷ idle_max ) = (idle_run ÷ idle_max )) ” 
  &&  “ ((idle_run ÷ idle_max ) > 100) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRecalibrate ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) usage_written X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (usage_written)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (usage_written)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (usage_written)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (usage_written)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (usage_written)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask usage_written )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((idle_run ÷ idle_max ) > 100)) (PreH2 : (idle_max <> 0)) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH8 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH9 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  TT && emp 
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRecalibrate ((task_stat_sample (idle_run) (idle_max))))) (sample_caller) (sample_mask)) sample_state X ) ” 
  &&  “ (0 = (task_stat_usage (sample_state))) ”
  &&  emp
).

Definition OS_TaskStat_entail_wit_18_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((idle_run ÷ idle_max ) > 100)) (PreH2 : (idle_max <> 0)) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH8 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH9 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRecalibrate ((task_stat_sample (idle_run) (idle_max))))) (sample_caller) (sample_mask)) sample_state X )
.

Definition OS_TaskStat_entail_wit_18_split_goal_2 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((idle_run ÷ idle_max ) > 100)) (PreH2 : (idle_max <> 0)) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH8 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH9 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  (0 = (task_stat_usage (sample_state)))
.

Definition OS_TaskStat_entail_wit_19_1 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : (idle_max = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH9 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
|--
  EX (hook_caller: TaskSuspendCaller)  (hook_mask: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((task_stat_run (sample_state)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (sample_state)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (sample_state)) <= UINT_MAX)) (PreH4 : ((task_stat_run (sample_state)) >= 0)) (PreH5 : ((task_stat_maximum (sample_state)) >= 0)) (PreH6 : ((task_stat_counter (sample_state)) >= 0)) (PreH7 : (idle_max = 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH13 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH14 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH15 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
|--
  EX (hook_caller: TaskSuspendCaller)  (hook_mask: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
).

Definition OS_TaskStat_entail_wit_19_2 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((idle_run ÷ idle_max ) <= 100)) (PreH2 : (idle_max <> 0)) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH8 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH9 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (100 - (idle_run ÷ idle_max ) ))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |-> (idle_run ÷ idle_max ))
|--
  EX (hook_caller: TaskSuspendCaller)  (hook_mask: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (sample_caller: TaskSuspendCaller) (sample_state: UCOS2_Verify_State) (sample_mask: Z) (PreH1 : ((task_stat_run (sample_state)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (sample_state)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (sample_state)) <= UINT_MAX)) (PreH4 : ((task_stat_run (sample_state)) >= 0)) (PreH5 : ((task_stat_maximum (sample_state)) >= 0)) (PreH6 : ((task_stat_counter (sample_state)) >= 0)) (PreH7 : ((idle_run ÷ idle_max ) <= 100)) (PreH8 : (idle_max <> 0)) (PreH9 : (task_stat_configuration sg )) (PreH10 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH11 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH14 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH15 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatUsage ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) sample_state X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (sample_state)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (sample_state)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (sample_state)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (100 - (idle_run ÷ idle_max ) ))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (sample_state)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask sample_state )
  **  (frame )
|--
  EX (hook_caller: TaskSuspendCaller)  (hook_mask: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
).

Definition OS_TaskStat_entail_wit_19_3 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (sample_caller: TaskSuspendCaller) (sample_mask: Z) (usage_written: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (idle_pct: Z) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH6 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH7 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH8 : (idle_pct = (idle_run ÷ idle_max ))) (PreH9 : (idle_pct > 100)) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRecalibrate ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) usage_written X )) ,
  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  ((( &( "idle_pct" ) )) # UInt  |-> idle_pct)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (usage_written)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (unsigned_last_nbits ((idle_run ÷ 100 )) (32)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (usage_written)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (usage_written)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (usage_written)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask usage_written )
  **  (frame )
|--
  EX (hook_caller: TaskSuspendCaller)  (hook_mask: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (capture_acquired: UCOS2_Verify_State) (sample_caller: TaskSuspendCaller) (sample_mask: Z) (usage_written: UCOS2_Verify_State) (idle_run: Z) (idle_max: Z) (idle_pct: Z) (PreH1 : ((task_stat_run (usage_written)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((idle_run ÷ 100 )) (32)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (usage_written)) <= UINT_MAX)) (PreH4 : ((task_stat_run (usage_written)) >= 0)) (PreH5 : ((unsigned_last_nbits ((idle_run ÷ 100 )) (32)) >= 0)) (PreH6 : ((task_stat_counter (usage_written)) >= 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH12 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH13 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) (PreH14 : (idle_pct = (idle_run ÷ idle_max ))) (PreH15 : (idle_pct > 100)) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRecalibrate ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (sample_caller) (sample_mask)) usage_written X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (usage_written)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (unsigned_last_nbits ((idle_run ÷ 100 )) (32)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (usage_written)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (usage_written)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (usage_written)))
  **  (task_stat_closed_statistics_frame environment saved_local sg sample_caller sample_mask usage_written )
  **  (frame )
|--
  EX (hook_caller: TaskSuspendCaller)  (hook_mask: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
).

Definition OS_TaskStat_entail_wit_20 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (stack_returned: TaskSuspendCaller) (stack_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick stack_returned hook_mask stack_current X )
|--
  EX (lc: TaskSuspendCaller)  (lm: Z)  (ls: UCOS2_Verify_State) ,
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
.

Definition OS_TaskStat_partial_solve_wit_1_pure := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (p_arg_pre = argument)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
  **  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OS_TaskStat_partial_solve_wit_1_aux := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (p_arg_pre = argument)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> p_arg_pre)
  **  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
.

Definition OS_TaskStat_partial_solve_wit_1 := OS_TaskStat_partial_solve_wit_1_pure -> OS_TaskStat_partial_solve_wit_1_aux.

Definition OS_TaskStat_partial_solve_wit_2_pure := 
(
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH12 : (p_arg_pre = argument)) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ ((task_stat_ready (rs)) = 0) ”
) \/
(
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (rs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (rs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (rs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (rs)) >= 0)) (PreH5 : ((task_stat_maximum (rs)) >= 0)) (PreH6 : ((task_stat_counter (rs)) >= 0)) (PreH7 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH18 : (p_arg_pre = argument)) (PreH19 : (task_stat_configuration sg )) (PreH20 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH21 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((task_stat_ready (rs)) = 0) ”
).

Definition OS_TaskStat_partial_solve_wit_2_pure_split_goal_1 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (rs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (rs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (rs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (rs)) >= 0)) (PreH5 : ((task_stat_maximum (rs)) >= 0)) (PreH6 : ((task_stat_counter (rs)) >= 0)) (PreH7 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH18 : (p_arg_pre = argument)) (PreH19 : (task_stat_configuration sg )) (PreH20 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH21 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((task_stat_ready (rs)) = 0) ”
.

Definition OS_TaskStat_partial_solve_wit_2_aux := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH12 : (p_arg_pre = argument)) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ ((task_stat_ready (rs)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_2 := OS_TaskStat_partial_solve_wit_2_pure -> OS_TaskStat_partial_solve_wit_2_aux.

Definition OS_TaskStat_partial_solve_wit_3 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH11 : (task_stat_configuration sg )) (PreH12 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH16 : (p_arg_pre = argument)) (PreH17 : (task_stat_configuration sg )) (PreH18 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH19 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
.

Definition OS_TaskStat_partial_solve_wit_4_pure := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (((2 * 100 ) ÷ 10 ) = 20) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ”
.

Definition OS_TaskStat_partial_solve_wit_4_aux := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
|--
  “ (((2 * 100 ) ÷ 10 ) = 20) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ” 
  &&  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
.

Definition OS_TaskStat_partial_solve_wit_4 := OS_TaskStat_partial_solve_wit_4_pure -> OS_TaskStat_partial_solve_wit_4_aux.

Definition OS_TaskStat_partial_solve_wit_5 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_post environment critical saved_local sg rc rm 20 rs frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )
|--
  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (time_dly_call_post environment critical saved_local sg rc rm 20 rs frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )
.

Definition OS_TaskStat_partial_solve_wit_6_pure := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OS_TaskStat_partial_solve_wit_6_aux := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH17 : (p_arg_pre = argument)) (PreH18 : (task_stat_configuration sg )) (PreH19 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH20 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
.

Definition OS_TaskStat_partial_solve_wit_6 := OS_TaskStat_partial_solve_wit_6_pure -> OS_TaskStat_partial_solve_wit_6_aux.

Definition OS_TaskStat_partial_solve_wit_7_pure := 
(
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH12 : (p_arg_pre = argument)) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ ((task_stat_ready (rs)) <> 0) ”
) \/
(
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (rs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (rs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (rs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (rs)) >= 0)) (PreH5 : ((task_stat_maximum (rs)) >= 0)) (PreH6 : ((task_stat_counter (rs)) >= 0)) (PreH7 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH18 : (p_arg_pre = argument)) (PreH19 : (task_stat_configuration sg )) (PreH20 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH21 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((task_stat_ready (rs)) <> 0) ”
).

Definition OS_TaskStat_partial_solve_wit_7_pure_split_goal_1 := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (rs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (rs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (rs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (rs)) >= 0)) (PreH5 : ((task_stat_maximum (rs)) >= 0)) (PreH6 : ((task_stat_counter (rs)) >= 0)) (PreH7 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH18 : (p_arg_pre = argument)) (PreH19 : (task_stat_configuration sg )) (PreH20 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH21 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((task_stat_ready (rs)) <> 0) ”
.

Definition OS_TaskStat_partial_solve_wit_7_aux := 
forall (p_arg_pre: Z) (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X )) (PreH12 : (p_arg_pre = argument)) (PreH13 : (task_stat_configuration sg )) (PreH14 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ ((task_stat_ready (rs)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((task_stat_ready (rs))) (32)) <> 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ” 
  &&  “ (p_arg_pre = argument) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_7 := OS_TaskStat_partial_solve_wit_7_pure -> OS_TaskStat_partial_solve_wit_7_aux.

Definition OS_TaskStat_partial_solve_wit_8_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((task_stat_maximum (zs)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ”
.

Definition OS_TaskStat_partial_solve_wit_8_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  “ ((task_stat_maximum (zs)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ ((task_stat_maximum (zs)) = 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_8 := OS_TaskStat_partial_solve_wit_8_pure -> OS_TaskStat_partial_solve_wit_8_aux.

Definition OS_TaskStat_partial_solve_wit_9_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (task_stat_configuration sg ) ”
.

Definition OS_TaskStat_partial_solve_wit_9_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
.

Definition OS_TaskStat_partial_solve_wit_9 := OS_TaskStat_partial_solve_wit_9_pure -> OS_TaskStat_partial_solve_wit_9_aux.

Definition OS_TaskStat_partial_solve_wit_10_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_call_pre environment critical saved_local sg zc zm zero_written 255 frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (255 = 255) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) ) ”
.

Definition OS_TaskStat_partial_solve_wit_10_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_call_pre environment critical saved_local sg zc zm zero_written 255 frame )
|--
  “ (255 = 255) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_suspend_call_pre environment critical saved_local sg zc zm zero_written 255 frame )
.

Definition OS_TaskStat_partial_solve_wit_10 := OS_TaskStat_partial_solve_wit_10_pure -> OS_TaskStat_partial_solve_wit_10_aux.

Definition OS_TaskStat_partial_solve_wit_11_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((task_stat_maximum (zs)) <> 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ”
.

Definition OS_TaskStat_partial_solve_wit_11_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  “ ((task_stat_maximum (zs)) <> 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ ((task_stat_maximum (zs)) <> 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_11 := OS_TaskStat_partial_solve_wit_11_pure -> OS_TaskStat_partial_solve_wit_11_aux.

Definition OS_TaskStat_partial_solve_wit_12 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((task_stat_maximum (zs)) <> 0)) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH11 : (task_stat_configuration sg )) (PreH12 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH13 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_stat_maximum (zs)) <> 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
.

Definition OS_TaskStat_partial_solve_wit_13 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scaled_caller: TaskSuspendCaller) (scaled_mask: Z) (scaled: UCOS2_Verify_State) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : ((task_stat_maximum (zs)) <> 0)) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) (PreH12 : (task_stat_configuration sg )) (PreH13 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X )) ,
  (task_suspend_closed environment critical saved_local sg zc zm zs )
  **  (frame )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_stat_maximum (zs)) <> 0) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (scaled_caller) (scaled_mask)) scaled X ) ”
  &&  (task_suspend_closed environment critical saved_local sg zc zm zs )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_14_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (cpu_sr: Z) (init_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_masked environment critical saved_local sg init_caller cpu_sr init_acquired init_released )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TaskStat_partial_solve_wit_14_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zm: Z) (init_caller: TaskSuspendCaller) (init_acquired: UCOS2_Verify_State) (cpu_sr: Z) (init_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X )) ,
  (task_suspend_masked environment critical saved_local sg init_caller cpu_sr init_acquired init_released )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatInitialize) (cpu_sr) (init_acquired) ((task_stat_sample (0) (0))))) (init_caller) (zm)) init_released X ) ”
  &&  (task_suspend_masked environment critical saved_local sg init_caller cpu_sr init_acquired init_released )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_14 := OS_TaskStat_partial_solve_wit_14_pure -> OS_TaskStat_partial_solve_wit_14_aux.

Definition OS_TaskStat_partial_solve_wit_15 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_configuration sg )) (PreH6 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
.

Definition OS_TaskStat_partial_solve_wit_16_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (1 = 1) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ”
.

Definition OS_TaskStat_partial_solve_wit_16_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
|--
  “ (1 = 1) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ” 
  &&  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
.

Definition OS_TaskStat_partial_solve_wit_16 := OS_TaskStat_partial_solve_wit_16_pure -> OS_TaskStat_partial_solve_wit_16_aux.

Definition OS_TaskStat_partial_solve_wit_17 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_post environment critical saved_local sg lc lm 1 ls frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )
|--
  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (time_dly_call_post environment critical saved_local sg lc lm 1 ls frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )
.

Definition OS_TaskStat_partial_solve_wit_18 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
|--
  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
.

Definition OS_TaskStat_partial_solve_wit_19 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X )) (PreH2 : (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stat_configuration sg )) (PreH8 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_closed environment critical saved_local sg one_returned lm one_current )
  **  (frame )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X ) ” 
  &&  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_suspend_closed environment critical saved_local sg one_returned lm one_current )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_20_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (cpu_sr: Z) (reset_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_masked environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_released )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TaskStat_partial_solve_wit_20_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (reset_caller: TaskSuspendCaller) (reset_acquired: UCOS2_Verify_State) (cpu_sr: Z) (reset_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X )) ,
  (task_suspend_masked environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_released )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatReset) (cpu_sr) (reset_acquired) ((task_stat_sample (0) (0))))) (reset_caller) (lm)) reset_released X ) ”
  &&  (task_suspend_masked environment critical saved_local sg reset_caller cpu_sr reset_acquired reset_released )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_20 := OS_TaskStat_partial_solve_wit_20_pure -> OS_TaskStat_partial_solve_wit_20_aux.

Definition OS_TaskStat_partial_solve_wit_21 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
.

Definition OS_TaskStat_partial_solve_wit_22_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (PreH1 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ ((100 ÷ 10 ) = 10) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ”
.

Definition OS_TaskStat_partial_solve_wit_22_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (PreH1 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
|--
  “ ((100 ÷ 10 ) = 10) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ” 
  &&  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
.

Definition OS_TaskStat_partial_solve_wit_22 := OS_TaskStat_partial_solve_wit_22_pure -> OS_TaskStat_partial_solve_wit_22_aux.

Definition OS_TaskStat_partial_solve_wit_23 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (PreH1 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (time_dly_call_post environment critical saved_local sg window_caller window_mask 10 window_state frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )
|--
  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (time_dly_call_post environment critical saved_local sg window_caller window_mask 10 window_state frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )
.

Definition OS_TaskStat_partial_solve_wit_24 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) (PreH1 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
|--
  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
.

Definition OS_TaskStat_partial_solve_wit_25 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) (PreH1 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X )) (PreH2 : (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )) (PreH3 : (task_stat_configuration sg )) (PreH4 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_closed environment critical saved_local sg window_returned window_mask window_current )
  **  (frame )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X ) ” 
  &&  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_suspend_closed environment critical saved_local sg window_returned window_mask window_current )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_26_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (cpu_sr: Z) (idle_run: Z) (idle_max: Z) (capture_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) ,
  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "idle_run" ) )) # UInt  |-> idle_run)
  **  ((( &( "idle_max" ) )) # UInt  |-> idle_max)
  **  (task_suspend_masked environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_released )
  **  (frame )
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TaskStat_partial_solve_wit_26_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (capture_caller: TaskSuspendCaller) (capture_acquired: UCOS2_Verify_State) (cpu_sr: Z) (idle_run: Z) (idle_max: Z) (capture_released: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X )) (PreH6 : (idle_run = (task_stat_counter (capture_acquired)))) (PreH7 : (idle_max = (task_stat_maximum (capture_acquired)))) (PreH8 : (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) )) ,
  (task_suspend_masked environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_released )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatRelease (TaskStatCapture) (cpu_sr) (capture_acquired) ((task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired))))))) (capture_caller) (window_mask)) capture_released X ) ” 
  &&  “ (idle_run = (task_stat_counter (capture_acquired))) ” 
  &&  “ (idle_max = (task_stat_maximum (capture_acquired))) ” 
  &&  “ (valid_statistics_sample (task_stat_sample ((task_stat_counter (capture_acquired))) ((task_stat_maximum (capture_acquired)))) ) ”
  &&  (task_suspend_masked environment critical saved_local sg capture_caller cpu_sr capture_acquired capture_released )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_26 := OS_TaskStat_partial_solve_wit_26_pure -> OS_TaskStat_partial_solve_wit_26_aux.

Definition OS_TaskStat_partial_solve_wit_27 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
.

Definition OS_TaskStat_partial_solve_wit_28 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
.

Definition OS_TaskStat_partial_solve_wit_29_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (task_stat_configuration sg ) ”
.

Definition OS_TaskStat_partial_solve_wit_29_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
.

Definition OS_TaskStat_partial_solve_wit_29 := OS_TaskStat_partial_solve_wit_29_pure -> OS_TaskStat_partial_solve_wit_29_aux.

Definition OS_TaskStat_partial_solve_wit_30_pure := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (argument: Z) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_closed environment critical saved_local sg hook_caller hook_mask hook_state )
  **  (frame )
  **  ((( &( "p_arg" ) )) # Ptr  |-> argument)
  **  ((( &( "idle_pct" ) )) # UInt  |->_)
  **  ((( &( "idle_max" ) )) # UInt  |->_)
  **  ((( &( "idle_run" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ”
.

Definition OS_TaskStat_partial_solve_wit_30_aux := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_suspend_closed environment critical saved_local sg hook_caller hook_mask hook_state )
  **  (frame )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_suspend_closed environment critical saved_local sg hook_caller hook_mask hook_state )
  **  (frame )
.

Definition OS_TaskStat_partial_solve_wit_30 := OS_TaskStat_partial_solve_wit_30_pure -> OS_TaskStat_partial_solve_wit_30_aux.

Definition OS_TaskStat_partial_solve_wit_31 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )) (PreH6 : (task_stat_configuration sg )) (PreH7 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_stk_chk_continuation_post environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ” 
  &&  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_stk_chk_continuation_post environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )
.

Definition OS_TaskStat_which_implies_wit_1 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (before)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (before)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (before)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (before)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (before)))
  **  (task_stat_closed_statistics_frame environment saved_local sg original initial_mask before )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (before)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (before)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (before)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (before)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (before)))
  **  (task_stat_closed_statistics_frame environment saved_local sg original initial_mask before )
  **  (frame )
).

Definition OS_TaskStat_which_implies_wit_1_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (original) (initial_mask)) before X ) ”
.

Definition OS_TaskStat_which_implies_wit_1_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (before: UCOS2_Verify_State) (initial_mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady original initial_mask before X )
|--
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (before)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (before)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (before)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (before)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (before)))
  **  (task_stat_closed_statistics_frame environment saved_local sg original initial_mask before )
  **  (frame )
.

Definition OS_TaskStat_which_implies_wit_2 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_ready (rs)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (rs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (rs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (rs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (rs)) >= 0)) (PreH5 : ((task_stat_maximum (rs)) >= 0)) (PreH6 : ((task_stat_counter (rs)) >= 0)) (PreH7 : ((task_stat_ready (rs)) = 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
).

Definition OS_TaskStat_which_implies_wit_2_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (rs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (rs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (rs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (rs)) >= 0)) (PreH5 : ((task_stat_maximum (rs)) >= 0)) (PreH6 : ((task_stat_counter (rs)) >= 0)) (PreH7 : ((task_stat_ready (rs)) = 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
.

Definition OS_TaskStat_which_implies_wit_3 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
|--
  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
|--
  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
).

Definition OS_TaskStat_which_implies_wit_3_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
|--
  “ (time_dly_safe environment critical sg rc rm 20 rs (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) ) ”
.

Definition OS_TaskStat_which_implies_wit_3_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReadyDelay rc rm rs X )
|--
  (time_dly_call_pre environment critical saved_local sg rc rm 20 rs frame )
.

Definition OS_TaskStat_which_implies_wit_4 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) ,
  (time_dly_call_post environment critical saved_local sg rc rm 20 rs frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )
|--
  EX (ready_returned: TaskSuspendCaller)  (ready_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) ,
  (time_dly_call_post environment critical saved_local sg rc rm 20 rs frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatReadyDelay) (rc) (rm) (20) (TaskStatReady) (rs) (X)) )
|--
  EX (ready_returned: TaskSuspendCaller)  (ready_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
).

Definition OS_TaskStat_which_implies_wit_5 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rm: Z) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (ready_returned) (rm)) ready_current X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (ready_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (ready_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (ready_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (ready_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (ready_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg ready_returned rm ready_current )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rm: Z) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (ready_returned) (rm)) ready_current X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (ready_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (ready_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (ready_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (ready_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (ready_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg ready_returned rm ready_current )
  **  (frame )
).

Definition OS_TaskStat_which_implies_wit_5_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rm: Z) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (ready_returned) (rm)) ready_current X ) ”
.

Definition OS_TaskStat_which_implies_wit_5_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rm: Z) (ready_returned: TaskSuspendCaller) (ready_current: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) (PreH2 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatReady ready_returned rm ready_current X )
|--
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (ready_current)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (ready_current)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (ready_current)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (ready_current)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (ready_current)))
  **  (task_stat_closed_statistics_frame environment saved_local sg ready_returned rm ready_current )
  **  (frame )
.

Definition OS_TaskStat_which_implies_wit_6 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_ready (rs)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (rs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (rs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (rs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (rs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (rs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg rc rm rs )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_ready (rs)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) ,
  TT && emp 
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X ) ”
  &&  emp
).

Definition OS_TaskStat_which_implies_wit_6_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (rc: TaskSuspendCaller) (rm: Z) (rs: UCOS2_Verify_State) (PreH1 : ((task_stat_ready (rs)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatReady) (rc) (rm)) rs X )) ,
  (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatScaleLoad) (rc) (rm)) rs X )
.

Definition OS_TaskStat_which_implies_wit_7 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroUsage) (zc) (zm)) zs X ) ”
  &&  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) ,
  TT && emp 
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroUsage) (zc) (zm)) zs X ) ”
  &&  emp
).

Definition OS_TaskStat_which_implies_wit_7_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) = 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) ,
  (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroUsage) (zc) (zm)) zs X )
.

Definition OS_TaskStat_which_implies_wit_8 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) ) ”
  &&  (task_suspend_call_pre environment critical saved_local sg zc zm zero_written 255 frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
|--
  “ (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) ) ”
  &&  (task_suspend_call_pre environment critical saved_local sg zc zm zero_written 255 frame )
).

Definition OS_TaskStat_which_implies_wit_8_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
|--
  “ (task_suspend_safe environment critical sg zc zm 255 zero_written (task_stat_suspend_observation (environment) (critical) (sg) (zc) (zm) (255) (zero_written) ((task_stat_suspend_continuation (environment) (critical) (saved_local) (sg) (frame) (zc) (zm) (zero_written) (X)))) ) ”
.

Definition OS_TaskStat_which_implies_wit_8_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zero_written: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSelfSuspend zc zm zero_written X )
|--
  (task_suspend_call_pre environment critical saved_local sg zc zm zero_written 255 frame )
.

Definition OS_TaskStat_which_implies_wit_9 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_maximum (zs)) <> 0)) (PreH2 : (task_stat_configuration sg )) (PreH3 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH4 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (zs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (zs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (zs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (zs)) >= 0)) (PreH5 : ((task_stat_maximum (zs)) >= 0)) (PreH6 : ((task_stat_counter (zs)) >= 0)) (PreH7 : ((task_stat_maximum (zs)) <> 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
).

Definition OS_TaskStat_which_implies_wit_9_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) (PreH1 : ((task_stat_run (zs)) <= UINT_MAX)) (PreH2 : ((task_stat_maximum (zs)) <= UINT_MAX)) (PreH3 : ((task_stat_counter (zs)) <= UINT_MAX)) (PreH4 : ((task_stat_run (zs)) >= 0)) (PreH5 : ((task_stat_maximum (zs)) >= 0)) (PreH6 : ((task_stat_counter (zs)) >= 0)) (PreH7 : ((task_stat_maximum (zs)) <> 0)) (PreH8 : (task_stat_configuration sg )) (PreH9 : (task_stat_statistics_addresses sg ( &( "OSIdleCtr" ) ) ( &( "OSIdleCtrMax" ) ) ( &( "OSIdleCtrRun" ) ) ( &( "OSCPUUsage" ) ) ( &( "OSStatRdy" ) ) )) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatZeroTest) (zc) (zm)) zs X )) ,
  ((( &( "OSIdleCtr" ) )) # UInt  |-> (task_stat_counter (zs)))
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> (task_stat_maximum (zs)))
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> (task_stat_run (zs)))
  **  ((( &( "OSCPUUsage" ) )) # UChar  |-> (task_stat_usage (zs)))
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> (task_stat_ready (zs)))
  **  (task_stat_closed_statistics_frame environment saved_local sg zc zm zs )
  **  (frame )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
.

Definition OS_TaskStat_which_implies_wit_10 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X ) ”
  &&  (task_suspend_closed environment critical saved_local sg zc zm zs )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X ) ”
  &&  (task_suspend_closed environment critical saved_local sg zc zm zs )
  **  (frame )
).

Definition OS_TaskStat_which_implies_wit_10_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatInitialize))) (zc) (zm)) zs X ) ”
.

Definition OS_TaskStat_which_implies_wit_10_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (zc: TaskSuspendCaller) (zm: Z) (zs: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatInitialize)) zc zm zs X )
|--
  (task_suspend_closed environment critical saved_local sg zc zm zs )
  **  (frame )
.

Definition OS_TaskStat_which_implies_wit_11 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
|--
  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
|--
  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
).

Definition OS_TaskStat_which_implies_wit_11_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
|--
  “ (time_dly_safe environment critical sg lc lm 1 ls (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) ) ”
.

Definition OS_TaskStat_which_implies_wit_11_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick lc lm ls X )
|--
  (time_dly_call_pre environment critical saved_local sg lc lm 1 ls frame )
.

Definition OS_TaskStat_which_implies_wit_12 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) ,
  (time_dly_call_post environment critical saved_local sg lc lm 1 ls frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )
|--
  EX (one_returned: TaskSuspendCaller)  (one_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lc: TaskSuspendCaller) (lm: Z) (ls: UCOS2_Verify_State) ,
  (time_dly_call_post environment critical saved_local sg lc lm 1 ls frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatOneTick) (lc) (lm) (1) ((TaskStatAcquire (TaskStatReset))) (ls) (X)) )
|--
  EX (one_returned: TaskSuspendCaller)  (one_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
).

Definition OS_TaskStat_which_implies_wit_13 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X ) ”
  &&  (task_suspend_closed environment critical saved_local sg one_returned lm one_current )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X ) ”
  &&  (task_suspend_closed environment critical saved_local sg one_returned lm one_current )
  **  (frame )
).

Definition OS_TaskStat_which_implies_wit_13_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatReset))) (one_returned) (lm)) one_current X ) ”
.

Definition OS_TaskStat_which_implies_wit_13_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (lm: Z) (one_returned: TaskSuspendCaller) (one_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatReset)) one_returned lm one_current X )
|--
  (task_suspend_closed environment critical saved_local sg one_returned lm one_current )
  **  (frame )
.

Definition OS_TaskStat_which_implies_wit_14 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
|--
  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
|--
  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ”
  &&  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
).

Definition OS_TaskStat_which_implies_wit_14_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
|--
  “ (time_dly_safe environment critical sg window_caller window_mask 10 window_state (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) ) ”
.

Definition OS_TaskStat_which_implies_wit_14_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatSampleWindow window_caller window_mask window_state X )
|--
  (time_dly_call_pre environment critical saved_local sg window_caller window_mask 10 window_state frame )
.

Definition OS_TaskStat_which_implies_wit_15 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) ,
  (time_dly_call_post environment critical saved_local sg window_caller window_mask 10 window_state frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )
|--
  EX (window_returned: TaskSuspendCaller)  (window_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_caller: TaskSuspendCaller) (window_state: UCOS2_Verify_State) (window_mask: Z) ,
  (time_dly_call_post environment critical saved_local sg window_caller window_mask 10 window_state frame (task_stat_delay_continuation (environment) (critical) (saved_local) (sg) (frame) (TaskStatSampleWindow) (window_caller) (window_mask) (10) ((TaskStatAcquire (TaskStatCapture))) (window_state) (X)) )
|--
  EX (window_returned: TaskSuspendCaller)  (window_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
).

Definition OS_TaskStat_which_implies_wit_16 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X ) ”
  &&  (task_suspend_closed environment critical saved_local sg window_returned window_mask window_current )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X ) ”
  &&  (task_suspend_closed environment critical saved_local sg window_returned window_mask window_current )
  **  (frame )
).

Definition OS_TaskStat_which_implies_wit_16_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
|--
  “ (task_stat_context environment critical saved_local sg frame (task_stat_at ((TaskStatAcquire (TaskStatCapture))) (window_returned) (window_mask)) window_current X ) ”
.

Definition OS_TaskStat_which_implies_wit_16_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (window_mask: Z) (window_returned: TaskSuspendCaller) (window_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame (TaskStatAcquire (TaskStatCapture)) window_returned window_mask window_current X )
|--
  (task_suspend_closed environment critical saved_local sg window_returned window_mask window_current )
  **  (frame )
.

Definition OS_TaskStat_which_implies_wit_17 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
).

Definition OS_TaskStat_which_implies_wit_17_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatHook hook_caller hook_mask hook_state X )
|--
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
.

Definition OS_TaskStat_which_implies_wit_18 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (task_stat_configuration sg ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ”
  &&  (task_suspend_closed environment critical saved_local sg hook_caller hook_mask hook_state )
  **  (frame )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ”
  &&  (task_suspend_closed environment critical saved_local sg hook_caller hook_mask hook_state )
  **  (frame )
).

Definition OS_TaskStat_which_implies_wit_18_split_goal_1 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) ) ”
.

Definition OS_TaskStat_which_implies_wit_18_split_goal_2 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg hook_caller hook_mask frame hook_state ) ”
.

Definition OS_TaskStat_which_implies_wit_18_split_goal_3 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (UCOS2_state_inv sg hook_state ) ”
.

Definition OS_TaskStat_which_implies_wit_18_split_goal_4 := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  “ (task_stat_stk_chk_configuration sg ) ”
.

Definition OS_TaskStat_which_implies_wit_18_split_goal_spatial := 
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (task_stat_configuration sg )) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatStack hook_caller hook_mask hook_state X )
|--
  (task_suspend_closed environment critical saved_local sg hook_caller hook_mask hook_state )
  **  (frame )
.

Definition OS_TaskStat_which_implies_wit_19 := 
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) ,
  (task_stat_stk_chk_continuation_post environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )
|--
  EX (stack_returned: TaskSuspendCaller)  (stack_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick stack_returned hook_mask stack_current X )
) \/
(
forall (X: (TaskStatPoint -> (UCOS2_Verify_State -> Prop))) (frame: Assertion) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (hook_caller: TaskSuspendCaller) (hook_mask: Z) (hook_state: UCOS2_Verify_State) ,
  (task_stat_stk_chk_continuation_post environment critical saved_local sg hook_caller hook_mask frame hook_state (task_stat_stack_continuation (environment) (critical) (saved_local) (sg) (frame) (hook_caller) (hook_mask) (hook_state) (X)) )
|--
  EX (stack_returned: TaskSuspendCaller)  (stack_current: UCOS2_Verify_State) ,
  (task_stat_closed_checkpoint environment critical saved_local sg frame TaskStatOneTick stack_returned hook_mask stack_current X )
).

Module Type VC_Correct.


Axiom proof_of_OS_TaskStat_safety_wit_1 : OS_TaskStat_safety_wit_1.
Axiom proof_of_OS_TaskStat_safety_wit_2 : OS_TaskStat_safety_wit_2.
Axiom proof_of_OS_TaskStat_safety_wit_3 : OS_TaskStat_safety_wit_3.
Axiom proof_of_OS_TaskStat_safety_wit_4 : OS_TaskStat_safety_wit_4.
Axiom proof_of_OS_TaskStat_safety_wit_5 : OS_TaskStat_safety_wit_5.
Axiom proof_of_OS_TaskStat_safety_wit_6 : OS_TaskStat_safety_wit_6.
Axiom proof_of_OS_TaskStat_safety_wit_7 : OS_TaskStat_safety_wit_7.
Axiom proof_of_OS_TaskStat_safety_wit_8 : OS_TaskStat_safety_wit_8.
Axiom proof_of_OS_TaskStat_safety_wit_9 : OS_TaskStat_safety_wit_9.
Axiom proof_of_OS_TaskStat_safety_wit_10 : OS_TaskStat_safety_wit_10.
Axiom proof_of_OS_TaskStat_safety_wit_11 : OS_TaskStat_safety_wit_11.
Axiom proof_of_OS_TaskStat_safety_wit_12 : OS_TaskStat_safety_wit_12.
Axiom proof_of_OS_TaskStat_safety_wit_13 : OS_TaskStat_safety_wit_13.
Axiom proof_of_OS_TaskStat_entail_wit_1 : OS_TaskStat_entail_wit_1.
Axiom proof_of_OS_TaskStat_entail_wit_2 : OS_TaskStat_entail_wit_2.
Axiom proof_of_OS_TaskStat_entail_wit_3 : OS_TaskStat_entail_wit_3.
Axiom proof_of_OS_TaskStat_entail_wit_4 : OS_TaskStat_entail_wit_4.
Axiom proof_of_OS_TaskStat_entail_wit_5 : OS_TaskStat_entail_wit_5.
Axiom proof_of_OS_TaskStat_entail_wit_6 : OS_TaskStat_entail_wit_6.
Axiom proof_of_OS_TaskStat_entail_wit_7 : OS_TaskStat_entail_wit_7.
Axiom proof_of_OS_TaskStat_entail_wit_8 : OS_TaskStat_entail_wit_8.
Axiom proof_of_OS_TaskStat_entail_wit_9 : OS_TaskStat_entail_wit_9.
Axiom proof_of_OS_TaskStat_entail_wit_10 : OS_TaskStat_entail_wit_10.
Axiom proof_of_OS_TaskStat_entail_wit_11 : OS_TaskStat_entail_wit_11.
Axiom proof_of_OS_TaskStat_entail_wit_12 : OS_TaskStat_entail_wit_12.
Axiom proof_of_OS_TaskStat_entail_wit_13 : OS_TaskStat_entail_wit_13.
Axiom proof_of_OS_TaskStat_entail_wit_14 : OS_TaskStat_entail_wit_14.
Axiom proof_of_OS_TaskStat_entail_wit_15 : OS_TaskStat_entail_wit_15.
Axiom proof_of_OS_TaskStat_entail_wit_16 : OS_TaskStat_entail_wit_16.
Axiom proof_of_OS_TaskStat_entail_wit_17 : OS_TaskStat_entail_wit_17.
Axiom proof_of_OS_TaskStat_entail_wit_18 : OS_TaskStat_entail_wit_18.
Axiom proof_of_OS_TaskStat_entail_wit_19_1 : OS_TaskStat_entail_wit_19_1.
Axiom proof_of_OS_TaskStat_entail_wit_19_2 : OS_TaskStat_entail_wit_19_2.
Axiom proof_of_OS_TaskStat_entail_wit_19_3 : OS_TaskStat_entail_wit_19_3.
Axiom proof_of_OS_TaskStat_entail_wit_20 : OS_TaskStat_entail_wit_20.
Axiom proof_of_OS_TaskStat_partial_solve_wit_1_pure : OS_TaskStat_partial_solve_wit_1_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_1 : OS_TaskStat_partial_solve_wit_1.
Axiom proof_of_OS_TaskStat_partial_solve_wit_2_pure : OS_TaskStat_partial_solve_wit_2_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_2 : OS_TaskStat_partial_solve_wit_2.
Axiom proof_of_OS_TaskStat_partial_solve_wit_3 : OS_TaskStat_partial_solve_wit_3.
Axiom proof_of_OS_TaskStat_partial_solve_wit_4_pure : OS_TaskStat_partial_solve_wit_4_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_4 : OS_TaskStat_partial_solve_wit_4.
Axiom proof_of_OS_TaskStat_partial_solve_wit_5 : OS_TaskStat_partial_solve_wit_5.
Axiom proof_of_OS_TaskStat_partial_solve_wit_6_pure : OS_TaskStat_partial_solve_wit_6_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_6 : OS_TaskStat_partial_solve_wit_6.
Axiom proof_of_OS_TaskStat_partial_solve_wit_7_pure : OS_TaskStat_partial_solve_wit_7_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_7 : OS_TaskStat_partial_solve_wit_7.
Axiom proof_of_OS_TaskStat_partial_solve_wit_8_pure : OS_TaskStat_partial_solve_wit_8_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_8 : OS_TaskStat_partial_solve_wit_8.
Axiom proof_of_OS_TaskStat_partial_solve_wit_9_pure : OS_TaskStat_partial_solve_wit_9_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_9 : OS_TaskStat_partial_solve_wit_9.
Axiom proof_of_OS_TaskStat_partial_solve_wit_10_pure : OS_TaskStat_partial_solve_wit_10_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_10 : OS_TaskStat_partial_solve_wit_10.
Axiom proof_of_OS_TaskStat_partial_solve_wit_11_pure : OS_TaskStat_partial_solve_wit_11_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_11 : OS_TaskStat_partial_solve_wit_11.
Axiom proof_of_OS_TaskStat_partial_solve_wit_12 : OS_TaskStat_partial_solve_wit_12.
Axiom proof_of_OS_TaskStat_partial_solve_wit_13 : OS_TaskStat_partial_solve_wit_13.
Axiom proof_of_OS_TaskStat_partial_solve_wit_14_pure : OS_TaskStat_partial_solve_wit_14_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_14 : OS_TaskStat_partial_solve_wit_14.
Axiom proof_of_OS_TaskStat_partial_solve_wit_15 : OS_TaskStat_partial_solve_wit_15.
Axiom proof_of_OS_TaskStat_partial_solve_wit_16_pure : OS_TaskStat_partial_solve_wit_16_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_16 : OS_TaskStat_partial_solve_wit_16.
Axiom proof_of_OS_TaskStat_partial_solve_wit_17 : OS_TaskStat_partial_solve_wit_17.
Axiom proof_of_OS_TaskStat_partial_solve_wit_18 : OS_TaskStat_partial_solve_wit_18.
Axiom proof_of_OS_TaskStat_partial_solve_wit_19 : OS_TaskStat_partial_solve_wit_19.
Axiom proof_of_OS_TaskStat_partial_solve_wit_20_pure : OS_TaskStat_partial_solve_wit_20_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_20 : OS_TaskStat_partial_solve_wit_20.
Axiom proof_of_OS_TaskStat_partial_solve_wit_21 : OS_TaskStat_partial_solve_wit_21.
Axiom proof_of_OS_TaskStat_partial_solve_wit_22_pure : OS_TaskStat_partial_solve_wit_22_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_22 : OS_TaskStat_partial_solve_wit_22.
Axiom proof_of_OS_TaskStat_partial_solve_wit_23 : OS_TaskStat_partial_solve_wit_23.
Axiom proof_of_OS_TaskStat_partial_solve_wit_24 : OS_TaskStat_partial_solve_wit_24.
Axiom proof_of_OS_TaskStat_partial_solve_wit_25 : OS_TaskStat_partial_solve_wit_25.
Axiom proof_of_OS_TaskStat_partial_solve_wit_26_pure : OS_TaskStat_partial_solve_wit_26_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_26 : OS_TaskStat_partial_solve_wit_26.
Axiom proof_of_OS_TaskStat_partial_solve_wit_27 : OS_TaskStat_partial_solve_wit_27.
Axiom proof_of_OS_TaskStat_partial_solve_wit_28 : OS_TaskStat_partial_solve_wit_28.
Axiom proof_of_OS_TaskStat_partial_solve_wit_29_pure : OS_TaskStat_partial_solve_wit_29_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_29 : OS_TaskStat_partial_solve_wit_29.
Axiom proof_of_OS_TaskStat_partial_solve_wit_30_pure : OS_TaskStat_partial_solve_wit_30_pure.
Axiom proof_of_OS_TaskStat_partial_solve_wit_30 : OS_TaskStat_partial_solve_wit_30.
Axiom proof_of_OS_TaskStat_partial_solve_wit_31 : OS_TaskStat_partial_solve_wit_31.
Axiom proof_of_OS_TaskStat_which_implies_wit_1 : OS_TaskStat_which_implies_wit_1.
Axiom proof_of_OS_TaskStat_which_implies_wit_2 : OS_TaskStat_which_implies_wit_2.
Axiom proof_of_OS_TaskStat_which_implies_wit_3 : OS_TaskStat_which_implies_wit_3.
Axiom proof_of_OS_TaskStat_which_implies_wit_4 : OS_TaskStat_which_implies_wit_4.
Axiom proof_of_OS_TaskStat_which_implies_wit_5 : OS_TaskStat_which_implies_wit_5.
Axiom proof_of_OS_TaskStat_which_implies_wit_6 : OS_TaskStat_which_implies_wit_6.
Axiom proof_of_OS_TaskStat_which_implies_wit_7 : OS_TaskStat_which_implies_wit_7.
Axiom proof_of_OS_TaskStat_which_implies_wit_8 : OS_TaskStat_which_implies_wit_8.
Axiom proof_of_OS_TaskStat_which_implies_wit_9 : OS_TaskStat_which_implies_wit_9.
Axiom proof_of_OS_TaskStat_which_implies_wit_10 : OS_TaskStat_which_implies_wit_10.
Axiom proof_of_OS_TaskStat_which_implies_wit_11 : OS_TaskStat_which_implies_wit_11.
Axiom proof_of_OS_TaskStat_which_implies_wit_12 : OS_TaskStat_which_implies_wit_12.
Axiom proof_of_OS_TaskStat_which_implies_wit_13 : OS_TaskStat_which_implies_wit_13.
Axiom proof_of_OS_TaskStat_which_implies_wit_14 : OS_TaskStat_which_implies_wit_14.
Axiom proof_of_OS_TaskStat_which_implies_wit_15 : OS_TaskStat_which_implies_wit_15.
Axiom proof_of_OS_TaskStat_which_implies_wit_16 : OS_TaskStat_which_implies_wit_16.
Axiom proof_of_OS_TaskStat_which_implies_wit_17 : OS_TaskStat_which_implies_wit_17.
Axiom proof_of_OS_TaskStat_which_implies_wit_18 : OS_TaskStat_which_implies_wit_18.
Axiom proof_of_OS_TaskStat_which_implies_wit_19 : OS_TaskStat_which_implies_wit_19.

End VC_Correct.
