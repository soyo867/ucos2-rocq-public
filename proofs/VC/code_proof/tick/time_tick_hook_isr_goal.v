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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_isr_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSTimeTickHook -----*)

Definition OSTimeTickHook_safety_wit_1 := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (app_time_tick_hook_step sg before before )) (PreH4 : (time_tick_entry sg invocation origin before )) (PreH5 : (0 <= counter)) (PreH6 : (counter <= 65535)) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> (time_tick_hook_advanced (counter)))
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
|--
  “ (10 <> 0) ”
.

Definition OSTimeTickHook_entail_wit_1 := 
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((time_tick_hook_advanced (counter))) (32)) >= (100 ÷ 10 ))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (app_time_tick_hook_step sg before before )) (PreH5 : (time_tick_entry sg invocation origin before )) (PreH6 : (0 <= counter)) (PreH7 : (counter <= 65535)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
) \/
(
forall (counter: Z) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((time_tick_hook_advanced (counter))) (32)) >= (100 ÷ 10 ))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (app_time_tick_hook_step sg before before )) (PreH5 : (time_tick_entry sg invocation origin before )) (PreH6 : (0 <= counter)) (PreH7 : (counter <= 65535)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ”
  &&  emp
).

Definition OSTimeTickHook_entail_wit_1_split_goal_1 := 
forall (counter: Z) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((time_tick_hook_advanced (counter))) (32)) >= (100 ÷ 10 ))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (app_time_tick_hook_step sg before before )) (PreH5 : (time_tick_entry sg invocation origin before )) (PreH6 : (0 <= counter)) (PreH7 : (counter <= 65535)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (10 <= (time_tick_hook_advanced (counter)))
.

Definition OSTimeTickHook_return_wit_1 := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after )) (PreH2 : (10 <= (time_tick_hook_advanced (counter)))) (PreH3 : (time_tick_signal_entry sg before )) (PreH4 : (event_table_layout_prop sg )) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
.

Definition OSTimeTickHook_return_wit_2 := 
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((time_tick_hook_advanced (counter))) (32)) < (100 ÷ 10 ))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (app_time_tick_hook_step sg before before )) (PreH5 : (time_tick_entry sg invocation origin before )) (PreH6 : (0 <= counter)) (PreH7 : (counter <= 65535)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> (time_tick_hook_advanced (counter)))
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
) \/
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((time_tick_hook_advanced (counter))) (32)) < (100 ÷ 10 ))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (app_time_tick_hook_step sg before before )) (PreH5 : (time_tick_entry sg invocation origin before )) (PreH6 : (0 <= counter)) (PreH7 : (counter <= 65535)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> (time_tick_hook_advanced (counter)))
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
).

Definition OSTimeTickHook_return_wit_2_split_goal_spatial := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((time_tick_hook_advanced (counter))) (32)) < (100 ÷ 10 ))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (app_time_tick_hook_step sg before before )) (PreH5 : (time_tick_entry sg invocation origin before )) (PreH6 : (0 <= counter)) (PreH7 : (counter <= 65535)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> (time_tick_hook_advanced (counter)))
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
.

Definition OSTimeTickHook_partial_solve_wit_1 := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin before )) (PreH2 : (0 <= counter)) (PreH3 : (counter <= 65535)) (PreH4 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH5 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (time_tick_entry sg invocation origin before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
.

Definition OSTimeTickHook_partial_solve_wit_2_pure := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (app_time_tick_hook_step sg before before )) (PreH2 : (time_tick_entry sg invocation origin before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (time_tick_entry sg invocation origin before ) ”
.

Definition OSTimeTickHook_partial_solve_wit_2_aux := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (app_time_tick_hook_step sg before before )) (PreH2 : (time_tick_entry sg invocation origin before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (time_tick_entry sg invocation origin before ) ” 
  &&  “ (app_time_tick_hook_step sg before before ) ” 
  &&  “ (time_tick_entry sg invocation origin before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
.

Definition OSTimeTickHook_partial_solve_wit_2 := OSTimeTickHook_partial_solve_wit_2_pure -> OSTimeTickHook_partial_solve_wit_2_aux.

Definition OSTimeTickHook_partial_solve_wit_3 := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (app_time_tick_hook_step sg before before )) (PreH4 : (time_tick_entry sg invocation origin before )) (PreH5 : (0 <= counter)) (PreH6 : (counter <= 65535)) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (app_time_tick_hook_step sg before before ) ” 
  &&  “ (time_tick_entry sg invocation origin before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
.

Definition OSTimeTickHook_partial_solve_wit_4_pure := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH5 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTickHook_partial_solve_wit_4_aux := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH5 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
.

Definition OSTimeTickHook_partial_solve_wit_4 := OSTimeTickHook_partial_solve_wit_4_pure -> OSTimeTickHook_partial_solve_wit_4_aux.

Definition OSTimeTickHook_partial_solve_wit_5_pure := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after )) (PreH2 : (10 <= (time_tick_hook_advanced (counter)))) (PreH3 : (time_tick_signal_entry sg before )) (PreH4 : (event_table_layout_prop sg )) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after ) ”
.

Definition OSTimeTickHook_partial_solve_wit_5_aux := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after )) (PreH2 : (10 <= (time_tick_hook_advanced (counter)))) (PreH3 : (time_tick_signal_entry sg before )) (PreH4 : (event_table_layout_prop sg )) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after ) ” 
  &&  “ (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after ) ” 
  &&  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
.

Definition OSTimeTickHook_partial_solve_wit_5 := OSTimeTickHook_partial_solve_wit_5_pure -> OSTimeTickHook_partial_solve_wit_5_aux.

Definition OSTimeTickHook_which_implies_wit_1 := 
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin before )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> counter)
) \/
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin before )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_signal_entry sg before ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> counter)
).

Definition OSTimeTickHook_which_implies_wit_1_split_goal_1 := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin before )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (event_table_layout_prop sg ) ”
.

Definition OSTimeTickHook_which_implies_wit_1_split_goal_2 := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin before )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (time_tick_signal_entry sg before ) ”
.

Definition OSTimeTickHook_which_implies_wit_1_split_goal_spatial := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin before )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter before )
|--
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> counter)
.

Definition OSTimeTickHook_which_implies_wit_2 := 
(
forall (counter: Z) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
|--
  ((( &( "OSTmrCtr" ) )) # UShort  |-> (time_tick_hook_advanced (counter)))
) \/
(
forall (counter: Z) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((counter + 1 )) (16)) = (time_tick_hook_advanced (counter))) ”
  &&  emp
).

Definition OSTimeTickHook_which_implies_wit_2_split_goal_1 := 
forall (counter: Z) ,
  ((unsigned_last_nbits ((counter + 1 )) (16)) = (time_tick_hook_advanced (counter)))
.

Definition OSTimeTickHook_which_implies_wit_3 := 
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (error: Z) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before error after )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
) \/
(
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (error: Z) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before error after )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
).

Definition OSTimeTickHook_which_implies_wit_3_split_goal_spatial := 
forall (counter: Z) (app_value: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (error: Z) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before error after )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  (time_tick_application_own application app_value )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry before app_value ( &( "OSTmrCtr" ) ) counter )
.

Module Type VC_Correct.


Axiom proof_of_OSTimeTickHook_safety_wit_1 : OSTimeTickHook_safety_wit_1.
Axiom proof_of_OSTimeTickHook_entail_wit_1 : OSTimeTickHook_entail_wit_1.
Axiom proof_of_OSTimeTickHook_return_wit_1 : OSTimeTickHook_return_wit_1.
Axiom proof_of_OSTimeTickHook_return_wit_2 : OSTimeTickHook_return_wit_2.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_1 : OSTimeTickHook_partial_solve_wit_1.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_2_pure : OSTimeTickHook_partial_solve_wit_2_pure.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_2 : OSTimeTickHook_partial_solve_wit_2.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_3 : OSTimeTickHook_partial_solve_wit_3.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_4_pure : OSTimeTickHook_partial_solve_wit_4_pure.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_4 : OSTimeTickHook_partial_solve_wit_4.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_5_pure : OSTimeTickHook_partial_solve_wit_5_pure.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_5 : OSTimeTickHook_partial_solve_wit_5.
Axiom proof_of_OSTimeTickHook_which_implies_wit_1 : OSTimeTickHook_which_implies_wit_1.
Axiom proof_of_OSTimeTickHook_which_implies_wit_2 : OSTimeTickHook_which_implies_wit_2.
Axiom proof_of_OSTimeTickHook_which_implies_wit_3 : OSTimeTickHook_which_implies_wit_3.

End VC_Correct.
