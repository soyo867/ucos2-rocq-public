From SimpleC.Verification Require Import VCPrelude.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_protocol_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.lib.task_idle_ready.
Import PrimitiveComponent.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_completed_caller_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_entry_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_source_call_spec.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (FlagPendActiveCaller.flag_pend_selected_caller_save_output (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before entry_heap retval )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH8 : (task_idle_ready sg (TskState (history_final)) )) (PreH9 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH10 : (os_sched_task_current_ready history_returned history_final )) (PreH11 : ((os_sched_ints (history_final)) = 0)) (PreH12 : ((os_sched_locks (history_final)) = 0)) (PreH13 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH14 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH15 : (task_idle_ready sg (TskState (history_final)) )) (PreH16 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH19 : (kernel_sched_ready_clients critical )) (PreH20 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH21 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH22 : (os_sched_active_local_stable active )) (PreH23 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH24 : (kernel_call_task_source history_scheduled history_entry )) (PreH25 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH26 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH27 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH28 : (interrupt_saved_value mask cpu_sr )) (PreH29 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH30 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH31 : (UCOS2_state_inv sg history_final )) (PreH32 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH33 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH34 : ((os_sched_ints (history_final)) = 0)) (PreH35 : ((os_sched_locks (history_final)) = 0)),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  “ (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask retval before save_scheduled save_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry ) ”
  &&  “ (task_tcb_init_stack_same_call save_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before save_entry ) ”
  &&  “ (interrupt_saved_value mask retval ) ”
  &&  “ (UCOS2_state_inv sg save_entry ) ”
  &&  “ (os_sched_call_cut sg save_scheduled save_entry ) ”
  &&  “ (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask retval before save_scheduled save_entry ) ”
  &&  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) retval save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask retval before save_scheduled save_entry ) ”
  &&  “ (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) ) ”
  &&  “ (UCOS2_state_inv sg save_entry ) ”
  &&  “ (interrupt_saved_value mask retval ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before save_entry ) ”
  &&  “ (task_tcb_init_stack_same_call save_scheduled context ) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask retval before save_scheduled save_entry ) ”
  &&  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) retval save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
).

Definition OS_Sched_entail_wit_1_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask retval before save_scheduled save_entry ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_2 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_3 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (UCOS2_state_inv sg save_entry ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_4 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (interrupt_saved_value mask retval ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_5 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (task_tcb_init_stack_source_preserved context before save_entry ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_6 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (task_tcb_init_stack_same_call save_scheduled context ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_7 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_8 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true) ”
.

Definition OS_Sched_entail_wit_1_split_goal_9 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask retval before save_scheduled save_entry ) ”
.

Definition OS_Sched_entail_wit_1_split_goal_spatial :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH6 : (kernel_call_normal_return context before save_scheduled save_entry )) (PreH7 : (kernel_call_control_rely sg before save_entry )) (PreH8 : (kernel_call_task_source save_scheduled save_entry )) (PreH9 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH10 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH11 : (task_idle_ready sg (TskState (save_entry)) )) (PreH12 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH13 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH14 : (os_sched_call_cut sg context before )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : ((os_sched_ints (before)) = 0)) (PreH18 : ((os_sched_locks (before)) = 0)) (PreH19 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH20 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH21 : (task_idle_ready sg (TskState (before)) )) (PreH22 : (flag_pend_non_idle_at sg context before )) (PreH23 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH24 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH25 : (kernel_call_task_source context before )) (PreH26 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH27 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : ((os_sched_ints (before)) = 0)) (PreH30 : ((os_sched_locks (before)) = 0)) (PreH31 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH32 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH33 : (task_idle_ready sg (TskState (before)) )) (PreH34 : (flag_pend_non_idle_at sg context before )) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH37 : (kernel_sched_ready_clients critical )) (PreH38 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH39 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH40 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH41 : (os_sched_active_local_stable active )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (kernel_call_stack_available context before )) (PreH44 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask retval before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
|--
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) retval save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
.

Definition OS_Sched_entail_wit_2 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH5 : (task_idle_ready sg (TskState (save_entry)) )) (PreH6 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH7 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH8 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH13 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH14 : (os_sched_active_local_stable active )) (PreH15 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH16 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH17 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH18 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH19 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (UCOS2_state_inv sg save_entry )) (PreH22 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH23 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH24 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (sched_new_priority ((os_sched_group (save_entry))) ((os_sched_rows (save_entry)))) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ (0 <= (os_sched_selected (entry))) ”
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH5 : (task_idle_ready sg (TskState (save_entry)) )) (PreH6 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH7 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH8 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH13 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH14 : (os_sched_active_local_stable active )) (PreH15 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH16 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH17 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH18 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH19 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (UCOS2_state_inv sg save_entry )) (PreH22 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH23 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH24 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (sched_new_priority ((os_sched_group (save_entry))) ((os_sched_rows (save_entry)))) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  (os_sched_fields_work_frame sg save_entry )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ ((os_sched_table (sg) (save_entry)) = (os_sched_table (sg) (entry))) ”
  &&  “ ((os_sched_counter (save_entry)) = (os_sched_counter (entry))) ”
  &&  “ ((os_sched_old_pointer (sg) (save_entry)) = (os_sched_old_pointer (sg) (entry))) ”
  &&  “ ((os_sched_current (save_entry)) = (os_sched_current (entry))) ”
  &&  “ ((os_sched_locks (save_entry)) = (os_sched_locks (entry))) ”
  &&  “ ((os_sched_ints (save_entry)) = (os_sched_ints (entry))) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ (0 <= (os_sched_selected (entry))) ”
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_sched_fields_work_frame sg entry )
).

Definition OS_Sched_entail_wit_3 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH2 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled_2)) entry_2 )) (PreH3 : (task_idle_ready sg (TskState (entry_2)) )) (PreH4 : (flag_pend_non_idle_at sg scheduled_2 entry_2 )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH7 : (kernel_sched_ready_clients critical )) (PreH8 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH9 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH10 : (os_sched_active_local_stable active )) (PreH11 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled_2 entry_2 )) (PreH12 : ((SchedStateDef.isRunning ((SchedState (entry_2)))) = true)) (PreH13 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled_2 entry_2 )) (PreH14 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH15 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (UCOS2_state_inv sg entry_2 )) (PreH18 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH19 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH20 : ((os_sched_ints (entry_2)) = 0)) (PreH21 : ((os_sched_locks (entry_2)) = 0)) (PreH22 : (0 <= (os_sched_selected (entry_2)))) (PreH23 : ((os_sched_selected (entry_2)) < 64)) (PreH24 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) (PreH25 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled_2 entry_2 )),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled_2 )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local_2 entry_2 )
  **  (active scheduled_2 entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled_2)) entry_2 )) (PreH5 : (task_idle_ready sg (TskState (entry_2)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled_2 entry_2 )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled_2 entry_2 )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry_2)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled_2 entry_2 )) (PreH16 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (UCOS2_state_inv sg entry_2 )) (PreH20 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH21 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH22 : ((os_sched_ints (entry_2)) = 0)) (PreH23 : ((os_sched_locks (entry_2)) = 0)) (PreH24 : (0 <= (os_sched_selected (entry_2)))) (PreH25 : ((os_sched_selected (entry_2)) < 64)) (PreH26 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) (PreH27 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled_2 entry_2 )),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled_2 )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local_2 entry_2 )
  **  (active scheduled_2 entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
).

Definition OS_Sched_entail_wit_4_1 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (os_sched_call_cut sg scheduled entry )) (PreH20 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (tmr_task_sched_switch_entry_output (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (os_sched_call_cut sg scheduled entry )) (PreH20 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (tmr_task_sched_switch_entry_output (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_2 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry)) = (os_sched_current (entry)))) (PreH2 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH3 : (task_idle_ready sg (TskState (entry)) )) (PreH4 : (flag_pend_non_idle_at sg scheduled entry )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH7 : (kernel_sched_ready_clients critical )) (PreH8 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH9 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH10 : (os_sched_active_local_stable active )) (PreH11 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH12 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH13 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH14 : (task_tcb_init_stack_same_call scheduled context )) (PreH15 : (task_tcb_init_stack_source_preserved context before entry )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (UCOS2_state_inv sg entry )) (PreH18 : (os_sched_call_cut sg scheduled entry )) (PreH19 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH20 : ((os_sched_ints (entry)) = 0)) (PreH21 : ((os_sched_locks (entry)) = 0)) (PreH22 : (0 <= (os_sched_selected (entry)))) (PreH23 : ((os_sched_selected (entry)) < 64)) (PreH24 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) (PreH25 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry)) >= 0)) (PreH3 : ((os_sched_selected (entry)) = (os_sched_current (entry)))) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (UCOS2_state_inv sg entry )) (PreH20 : (os_sched_call_cut sg scheduled entry )) (PreH21 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH22 : ((os_sched_ints (entry)) = 0)) (PreH23 : ((os_sched_locks (entry)) = 0)) (PreH24 : (0 <= (os_sched_selected (entry)))) (PreH25 : ((os_sched_selected (entry)) < 64)) (PreH26 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) (PreH27 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_3 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) <> 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH4 : (task_idle_ready sg (TskState (save_entry)) )) (PreH5 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH6 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH7 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH12 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH13 : (os_sched_active_local_stable active )) (PreH14 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH15 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH16 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH17 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH18 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (UCOS2_state_inv sg save_entry )) (PreH21 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH22 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH23 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((os_sched_counter (save_entry)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (save_entry)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) <> 0)) (PreH4 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH5 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH6 : (task_idle_ready sg (TskState (save_entry)) )) (PreH7 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH8 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH9 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH17 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH18 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH19 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH20 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH21 : (interrupt_saved_value mask cpu_sr )) (PreH22 : (UCOS2_state_inv sg save_entry )) (PreH23 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH24 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH25 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_4 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) <> 0)) (PreH2 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH3 : (task_idle_ready sg (TskState (save_entry)) )) (PreH4 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH5 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH6 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH16 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (UCOS2_state_inv sg save_entry )) (PreH20 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH21 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH22 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((os_sched_counter (save_entry)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (save_entry)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) <> 0)) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH5 : (task_idle_ready sg (TskState (save_entry)) )) (PreH6 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH7 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH8 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH13 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH14 : (os_sched_active_local_stable active )) (PreH15 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH16 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH17 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH18 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH19 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (UCOS2_state_inv sg save_entry )) (PreH22 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH23 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH24 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion)) (history_scheduled: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_returned: OsSchedCallContext) (history_final: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_return_wit_1 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH8 : (task_idle_ready sg (TskState (history_final)) )) (PreH9 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH10 : (os_sched_task_current_ready history_returned history_final )) (PreH11 : ((os_sched_ints (history_final)) = 0)) (PreH12 : ((os_sched_locks (history_final)) = 0)) (PreH13 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH14 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH15 : (task_idle_ready sg (TskState (history_final)) )) (PreH16 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH19 : (kernel_sched_ready_clients critical )) (PreH20 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH21 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH22 : (os_sched_active_local_stable active )) (PreH23 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH24 : (kernel_call_task_source history_scheduled history_entry )) (PreH25 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH26 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH27 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH28 : (interrupt_saved_value mask cpu_sr )) (PreH29 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH30 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH31 : (UCOS2_state_inv sg history_final )) (PreH32 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH33 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH34 : ((os_sched_ints (history_final)) = 0)) (PreH35 : ((os_sched_locks (history_final)) = 0)),
  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (tmr_task_sched_history_entry_post (task_sw_hook_call_environment (environment)) critical active sg context mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH8 : (task_idle_ready sg (TskState (history_final)) )) (PreH9 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH10 : (os_sched_task_current_ready history_returned history_final )) (PreH11 : ((os_sched_ints (history_final)) = 0)) (PreH12 : ((os_sched_locks (history_final)) = 0)) (PreH13 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH14 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH15 : (task_idle_ready sg (TskState (history_final)) )) (PreH16 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH19 : (kernel_sched_ready_clients critical )) (PreH20 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH21 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH22 : (os_sched_active_local_stable active )) (PreH23 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH24 : (kernel_call_task_source history_scheduled history_entry )) (PreH25 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH26 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH27 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH28 : (interrupt_saved_value mask cpu_sr )) (PreH29 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH30 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH31 : (UCOS2_state_inv sg history_final )) (PreH32 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH33 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH34 : ((os_sched_ints (history_final)) = 0)) (PreH35 : ((os_sched_locks (history_final)) = 0)),
  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  (tmr_task_sched_history_entry_post (task_sw_hook_call_environment (environment)) critical active sg context mask before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH8 : (task_idle_ready sg (TskState (history_final)) )) (PreH9 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH10 : (os_sched_task_current_ready history_returned history_final )) (PreH11 : ((os_sched_ints (history_final)) = 0)) (PreH12 : ((os_sched_locks (history_final)) = 0)) (PreH13 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH14 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH15 : (task_idle_ready sg (TskState (history_final)) )) (PreH16 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH19 : (kernel_sched_ready_clients critical )) (PreH20 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH21 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH22 : (os_sched_active_local_stable active )) (PreH23 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH24 : (kernel_call_task_source history_scheduled history_entry )) (PreH25 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH26 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH27 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH28 : (interrupt_saved_value mask cpu_sr )) (PreH29 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH30 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH31 : (UCOS2_state_inv sg history_final )) (PreH32 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH33 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH34 : ((os_sched_ints (history_final)) = 0)) (PreH35 : ((os_sched_locks (history_final)) = 0)),
  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  (tmr_task_sched_history_entry_post (task_sw_hook_call_environment (environment)) critical active sg context mask before )
.

Definition OS_Sched_partial_solve_wit_1_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH10 : (os_sched_active_local_stable active )) (PreH11 : (kernel_tcb_stack_field_layout sg )) (PreH12 : (kernel_call_stack_available context before )) (PreH13 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
.

Definition OS_Sched_partial_solve_wit_1_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH10 : (os_sched_active_local_stable active )) (PreH11 : (kernel_tcb_stack_field_layout sg )) (PreH12 : (kernel_call_stack_available context before )) (PreH13 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
.

Definition OS_Sched_partial_solve_wit_1 := OS_Sched_partial_solve_wit_1_pure -> OS_Sched_partial_solve_wit_1_aux.

Definition OS_Sched_partial_solve_wit_2_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH5 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH6 : (kernel_call_task_source context before )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : ((os_sched_locks (before)) = 0)) (PreH12 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH13 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH14 : (task_idle_ready sg (TskState (before)) )) (PreH15 : (flag_pend_non_idle_at sg context before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH18 : (kernel_sched_ready_clients critical )) (PreH19 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH20 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH21 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH22 : (os_sched_active_local_stable active )) (PreH23 : (kernel_tcb_stack_field_layout sg )) (PreH24 : (kernel_call_stack_available context before )) (PreH25 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
.

Definition OS_Sched_partial_solve_wit_2_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH5 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH6 : (kernel_call_task_source context before )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : ((os_sched_ints (before)) = 0)) (PreH11 : ((os_sched_locks (before)) = 0)) (PreH12 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH13 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH14 : (task_idle_ready sg (TskState (before)) )) (PreH15 : (flag_pend_non_idle_at sg context before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH18 : (kernel_sched_ready_clients critical )) (PreH19 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH20 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH21 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH22 : (os_sched_active_local_stable active )) (PreH23 : (kernel_tcb_stack_field_layout sg )) (PreH24 : (kernel_call_stack_available context before )) (PreH25 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_2 := OS_Sched_partial_solve_wit_2_pure -> OS_Sched_partial_solve_wit_2_aux.

Definition OS_Sched_partial_solve_wit_3_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
.

Definition OS_Sched_partial_solve_wit_3_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
|--
  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
.

Definition OS_Sched_partial_solve_wit_3 := OS_Sched_partial_solve_wit_3_pure -> OS_Sched_partial_solve_wit_3_aux.

Definition OS_Sched_partial_solve_wit_4_pure :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (context)) before ) ”
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (os_sched_call_cut sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : ((os_sched_ints (before)) = 0)) (PreH7 : ((os_sched_locks (before)) = 0)) (PreH8 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH9 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH10 : (task_idle_ready sg (TskState (before)) )) (PreH11 : (flag_pend_non_idle_at sg context before )) (PreH12 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH13 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH14 : (kernel_call_task_source context before )) (PreH15 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH16 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH17 : (os_sched_active_local_stable active )) (PreH18 : ((os_sched_ints (before)) = 0)) (PreH19 : ((os_sched_locks (before)) = 0)) (PreH20 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH21 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH22 : (task_idle_ready sg (TskState (before)) )) (PreH23 : (flag_pend_non_idle_at sg context before )) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH26 : (kernel_sched_ready_clients critical )) (PreH27 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH28 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH29 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH30 : (os_sched_active_local_stable active )) (PreH31 : (kernel_tcb_stack_field_layout sg )) (PreH32 : (kernel_call_stack_available context before )) (PreH33 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (context)) before ) ”
).

Definition OS_Sched_partial_solve_wit_4_pure_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (os_sched_call_cut sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : ((os_sched_ints (before)) = 0)) (PreH7 : ((os_sched_locks (before)) = 0)) (PreH8 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH9 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH10 : (task_idle_ready sg (TskState (before)) )) (PreH11 : (flag_pend_non_idle_at sg context before )) (PreH12 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH13 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH14 : (kernel_call_task_source context before )) (PreH15 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH16 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH17 : (os_sched_active_local_stable active )) (PreH18 : ((os_sched_ints (before)) = 0)) (PreH19 : ((os_sched_locks (before)) = 0)) (PreH20 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH21 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH22 : (task_idle_ready sg (TskState (before)) )) (PreH23 : (flag_pend_non_idle_at sg context before )) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH26 : (kernel_sched_ready_clients critical )) (PreH27 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH28 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH29 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH30 : (os_sched_active_local_stable active )) (PreH31 : (kernel_tcb_stack_field_layout sg )) (PreH32 : (kernel_call_stack_available context before )) (PreH33 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (context)) before ) ”
.

Definition OS_Sched_partial_solve_wit_4_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (context)) before ) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
.

Definition OS_Sched_partial_solve_wit_4 := OS_Sched_partial_solve_wit_4_pure -> OS_Sched_partial_solve_wit_4_aux.

Definition OS_Sched_partial_solve_wit_5_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (FlagPendActiveCaller.flag_pend_selected_caller_save_output (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before entry_heap retval )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
.

Definition OS_Sched_partial_solve_wit_5_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : ((os_sched_ints (before)) = 0)) (PreH5 : ((os_sched_locks (before)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH8 : (task_idle_ready sg (TskState (before)) )) (PreH9 : (flag_pend_non_idle_at sg context before )) (PreH10 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH11 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH12 : (kernel_call_task_source context before )) (PreH13 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH14 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH15 : (os_sched_active_local_stable active )) (PreH16 : ((os_sched_ints (before)) = 0)) (PreH17 : ((os_sched_locks (before)) = 0)) (PreH18 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH19 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH20 : (task_idle_ready sg (TskState (before)) )) (PreH21 : (flag_pend_non_idle_at sg context before )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH24 : (kernel_sched_ready_clients critical )) (PreH25 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH26 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH28 : (os_sched_active_local_stable active )) (PreH29 : (kernel_tcb_stack_field_layout sg )) (PreH30 : (kernel_call_stack_available context before )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (FlagPendActiveCaller.flag_pend_selected_caller_save_output (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before entry_heap retval )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  (FlagPendActiveCaller.flag_pend_selected_caller_save_output (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before entry_heap retval )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Definition OS_Sched_partial_solve_wit_6_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (os_sched_call_cut sg context before )) (PreH6 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH7 : (kernel_sched_ready_clients critical )) (PreH8 : ((os_sched_ints (before)) = 0)) (PreH9 : ((os_sched_locks (before)) = 0)) (PreH10 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH11 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH12 : (task_idle_ready sg (TskState (before)) )) (PreH13 : (flag_pend_non_idle_at sg context before )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH16 : (kernel_call_task_source context before )) (PreH17 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH18 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH19 : (os_sched_active_local_stable active )) (PreH20 : ((os_sched_ints (before)) = 0)) (PreH21 : ((os_sched_locks (before)) = 0)) (PreH22 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH23 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH24 : (task_idle_ready sg (TskState (before)) )) (PreH25 : (flag_pend_non_idle_at sg context before )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH28 : (kernel_sched_ready_clients critical )) (PreH29 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH30 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH32 : (os_sched_active_local_stable active )) (PreH33 : (kernel_tcb_stack_field_layout sg )) (PreH34 : (kernel_call_stack_available context before )) (PreH35 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (retval) (save_entry) (save_entry)) save_after_heap )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
.

Definition OS_Sched_partial_solve_wit_6_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (retval: Z) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH5 : (os_sched_call_cut sg context before )) (PreH6 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH7 : (kernel_sched_ready_clients critical )) (PreH8 : ((os_sched_ints (before)) = 0)) (PreH9 : ((os_sched_locks (before)) = 0)) (PreH10 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH11 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH12 : (task_idle_ready sg (TskState (before)) )) (PreH13 : (flag_pend_non_idle_at sg context before )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before )) (PreH16 : (kernel_call_task_source context before )) (PreH17 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH18 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH19 : (os_sched_active_local_stable active )) (PreH20 : ((os_sched_ints (before)) = 0)) (PreH21 : ((os_sched_locks (before)) = 0)) (PreH22 : (FlagPendEntryControl.flag_pend_active_entry sg active before )) (PreH23 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH24 : (task_idle_ready sg (TskState (before)) )) (PreH25 : (flag_pend_non_idle_at sg context before )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH28 : (kernel_sched_ready_clients critical )) (PreH29 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH30 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH31 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)) (PreH32 : (os_sched_active_local_stable active )) (PreH33 : (kernel_tcb_stack_field_layout sg )) (PreH34 : (kernel_call_stack_available context before )) (PreH35 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (retval) (save_entry) (save_entry)) save_after_heap )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask retval before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (kernel_call_stack_available context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (retval) (save_entry) (save_entry)) save_after_heap )
.

Definition OS_Sched_partial_solve_wit_6 := OS_Sched_partial_solve_wit_6_pure -> OS_Sched_partial_solve_wit_6_aux.

Definition OS_Sched_partial_solve_wit_7_pure :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH4 : (task_idle_ready sg (TskState (save_entry)) )) (PreH5 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH6 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH7 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH12 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH13 : (os_sched_active_local_stable active )) (PreH14 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH15 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH16 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH17 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH18 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (UCOS2_state_inv sg save_entry )) (PreH21 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH22 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH23 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((os_sched_counter (save_entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (save_entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH8 : (task_idle_ready sg (TskState (save_entry)) )) (PreH9 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH10 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH11 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH14 : (kernel_sched_ready_clients critical )) (PreH15 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH16 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH17 : (os_sched_active_local_stable active )) (PreH18 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH19 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH20 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH21 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH22 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH23 : (interrupt_saved_value mask cpu_sr )) (PreH24 : (UCOS2_state_inv sg save_entry )) (PreH25 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH26 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH27 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
).

Definition OS_Sched_partial_solve_wit_7_pure_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((os_sched_counter (save_entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (save_entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH7 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH8 : (task_idle_ready sg (TskState (save_entry)) )) (PreH9 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH10 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH11 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH14 : (kernel_sched_ready_clients critical )) (PreH15 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH16 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH17 : (os_sched_active_local_stable active )) (PreH18 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH19 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH20 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH21 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH22 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH23 : (interrupt_saved_value mask cpu_sr )) (PreH24 : (UCOS2_state_inv sg save_entry )) (PreH25 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH26 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH27 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_7_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (active_before: model) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH4 : (task_idle_ready sg (TskState (save_entry)) )) (PreH5 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH6 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )) (PreH7 : (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH12 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH13 : (os_sched_active_local_stable active )) (PreH14 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )) (PreH15 : ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true)) (PreH16 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry )) (PreH17 : (task_tcb_init_stack_same_call save_scheduled context )) (PreH18 : (task_tcb_init_stack_source_preserved context before save_entry )) (PreH19 : (interrupt_saved_value mask cpu_sr )) (PreH20 : (UCOS2_state_inv sg save_entry )) (PreH21 : (os_sched_call_cut sg save_scheduled save_entry )) (PreH22 : (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) )) (PreH23 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry )),
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
  &&  “ ((unsigned_last_nbits ((os_sched_locks (save_entry))) (32)) = 0) ”
  &&  “ ((unsigned_last_nbits ((os_sched_ints (save_entry))) (32)) = 0) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  “ (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (save_entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation save_scheduled save_entry ) ”
  &&  “ (task_tcb_init_stack_same_call save_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before save_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg save_entry ) ”
  &&  “ (os_sched_call_cut sg save_scheduled save_entry ) ”
  &&  “ (task_stack_live_coverage (TskState (save_entry)) (task_stack_call_active_key (save_scheduled)) ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before save_scheduled save_entry ) ”
  &&  (sched_new_rep sg (os_sched_group (save_entry)) (os_sched_rows (save_entry)) (os_sched_old_high (save_entry)) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (save_scheduled)) (os_sched_call_origin (save_scheduled)) cpu_sr save_entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) save_scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) save_local save_entry )
  **  (active save_scheduled save_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (save_entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (save_entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (save_entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (save_entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (save_entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (save_entry)))
  **  (os_sched_fields_work_frame sg save_entry )
.

Definition OS_Sched_partial_solve_wit_7 := OS_Sched_partial_solve_wit_7_pure -> OS_Sched_partial_solve_wit_7_aux.

Definition OS_Sched_partial_solve_wit_8 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH11 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH12 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH13 : (task_tcb_init_stack_same_call scheduled context )) (PreH14 : (task_tcb_init_stack_source_preserved context before entry )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (UCOS2_state_inv sg entry )) (PreH17 : (os_sched_call_cut sg scheduled entry )) (PreH18 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH19 : ((os_sched_ints (entry)) = 0)) (PreH20 : ((os_sched_locks (entry)) = 0)) (PreH21 : (0 <= (os_sched_selected (entry)))) (PreH22 : ((os_sched_selected (entry)) < 64)) (PreH23 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) (PreH24 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ (0 <= (os_sched_selected (entry))) ”
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((os_sched_selected (entry)) * sizeof(PTR)))) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (os_sched_selected (entry)) 0 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform ((task_sw_hook_call_environment (environment)))) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context (task_sw_hook_call_environment (environment)) scheduled )
  **  (os_sched_fields_capsules (task_sw_hook_call_environment (environment)) entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
.

Definition OS_Sched_partial_solve_wit_9_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH11 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH12 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH13 : (task_tcb_init_stack_same_call scheduled context )) (PreH14 : (task_tcb_init_stack_source_preserved context before entry )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (os_sched_call_cut sg scheduled entry )) (PreH17 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
.

Definition OS_Sched_partial_solve_wit_9_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH11 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH12 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH13 : (task_tcb_init_stack_same_call scheduled context )) (PreH14 : (task_tcb_init_stack_source_preserved context before entry )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (os_sched_call_cut sg scheduled entry )) (PreH17 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
.

Definition OS_Sched_partial_solve_wit_9 := OS_Sched_partial_solve_wit_9_pure -> OS_Sched_partial_solve_wit_9_aux.

Definition OS_Sched_partial_solve_wit_10_pure :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (os_sched_call_cut sg scheduled entry )) (PreH20 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH4 : (task_idle_ready sg (TskState (entry)) )) (PreH5 : (flag_pend_non_idle_at sg scheduled entry )) (PreH6 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH7 : (task_idle_ready sg (TskState (entry)) )) (PreH8 : (flag_pend_non_idle_at sg scheduled entry )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH13 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH14 : (os_sched_active_local_stable active )) (PreH15 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH16 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH17 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH18 : (task_tcb_init_stack_same_call scheduled context )) (PreH19 : (task_tcb_init_stack_source_preserved context before entry )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (os_sched_call_cut sg scheduled entry )) (PreH22 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
).

Definition OS_Sched_partial_solve_wit_10_pure_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH4 : (task_idle_ready sg (TskState (entry)) )) (PreH5 : (flag_pend_non_idle_at sg scheduled entry )) (PreH6 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH7 : (task_idle_ready sg (TskState (entry)) )) (PreH8 : (flag_pend_non_idle_at sg scheduled entry )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH13 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH14 : (os_sched_active_local_stable active )) (PreH15 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH16 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH17 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH18 : (task_tcb_init_stack_same_call scheduled context )) (PreH19 : (task_tcb_init_stack_source_preserved context before entry )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (os_sched_call_cut sg scheduled entry )) (PreH22 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ ((os_sched_ints (entry)) = 0) ”
.

Definition OS_Sched_partial_solve_wit_10_pure_split_goal_2 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH4 : (task_idle_ready sg (TskState (entry)) )) (PreH5 : (flag_pend_non_idle_at sg scheduled entry )) (PreH6 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH7 : (task_idle_ready sg (TskState (entry)) )) (PreH8 : (flag_pend_non_idle_at sg scheduled entry )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH13 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH14 : (os_sched_active_local_stable active )) (PreH15 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH16 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH17 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH18 : (task_tcb_init_stack_same_call scheduled context )) (PreH19 : (task_tcb_init_stack_source_preserved context before entry )) (PreH20 : (interrupt_saved_value mask cpu_sr )) (PreH21 : (os_sched_call_cut sg scheduled entry )) (PreH22 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ ((os_sched_locks (entry)) = 0) ”
.

Definition OS_Sched_partial_solve_wit_10_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (os_sched_call_cut sg scheduled entry )) (PreH20 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
.

Definition OS_Sched_partial_solve_wit_10 := OS_Sched_partial_solve_wit_10_pure -> OS_Sched_partial_solve_wit_10_aux.

Definition OS_Sched_partial_solve_wit_11_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (os_sched_call_cut sg scheduled entry )) (PreH20 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (tmr_task_sched_switch_source_post (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
.

Definition OS_Sched_partial_solve_wit_11_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH5 : (task_idle_ready sg (TskState (entry)) )) (PreH6 : (flag_pend_non_idle_at sg scheduled entry )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH11 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH12 : (os_sched_active_local_stable active )) (PreH13 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )) (PreH14 : ((SchedStateDef.isRunning ((SchedState (entry)))) = true)) (PreH15 : (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry )) (PreH16 : (task_tcb_init_stack_same_call scheduled context )) (PreH17 : (task_tcb_init_stack_source_preserved context before entry )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (os_sched_call_cut sg scheduled entry )) (PreH20 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry )),
  (tmr_task_sched_switch_source_post (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (entry)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (tmr_task_sched_switch_source_post (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
.

Definition OS_Sched_partial_solve_wit_11 := OS_Sched_partial_solve_wit_11_pure -> OS_Sched_partial_solve_wit_11_aux.

Definition OS_Sched_partial_solve_wit_12_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH11 : (kernel_call_task_source history_scheduled history_entry )) (PreH12 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH13 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH14 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH17 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH18 : (UCOS2_state_inv sg history_final )) (PreH19 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH20 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH21 : ((os_sched_ints (history_final)) = 0)) (PreH22 : ((os_sched_locks (history_final)) = 0)),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
.

Definition OS_Sched_partial_solve_wit_12_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH8 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH11 : (kernel_call_task_source history_scheduled history_entry )) (PreH12 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH13 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH14 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH17 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH18 : (UCOS2_state_inv sg history_final )) (PreH19 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH20 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH21 : ((os_sched_ints (history_final)) = 0)) (PreH22 : ((os_sched_locks (history_final)) = 0)),
  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_12 := OS_Sched_partial_solve_wit_12_pure -> OS_Sched_partial_solve_wit_12_aux.

Definition OS_Sched_partial_solve_wit_13_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (os_sched_task_current_ready history_returned history_final )) (PreH5 : ((os_sched_ints (history_final)) = 0)) (PreH6 : ((os_sched_locks (history_final)) = 0)) (PreH7 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH8 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH9 : (task_idle_ready sg (TskState (history_final)) )) (PreH10 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH13 : (kernel_sched_ready_clients critical )) (PreH14 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH15 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH16 : (os_sched_active_local_stable active )) (PreH17 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH18 : (kernel_call_task_source history_scheduled history_entry )) (PreH19 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH20 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH21 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH22 : (interrupt_saved_value mask cpu_sr )) (PreH23 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH24 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH25 : (UCOS2_state_inv sg history_final )) (PreH26 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH28 : ((os_sched_ints (history_final)) = 0)) (PreH29 : ((os_sched_locks (history_final)) = 0)),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
.

Definition OS_Sched_partial_solve_wit_13_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (os_sched_task_current_ready history_returned history_final )) (PreH5 : ((os_sched_ints (history_final)) = 0)) (PreH6 : ((os_sched_locks (history_final)) = 0)) (PreH7 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH8 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH9 : (task_idle_ready sg (TskState (history_final)) )) (PreH10 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH13 : (kernel_sched_ready_clients critical )) (PreH14 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH15 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH16 : (os_sched_active_local_stable active )) (PreH17 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH18 : (kernel_call_task_source history_scheduled history_entry )) (PreH19 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH20 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH21 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH22 : (interrupt_saved_value mask cpu_sr )) (PreH23 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH24 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH25 : (UCOS2_state_inv sg history_final )) (PreH26 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH27 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH28 : ((os_sched_ints (history_final)) = 0)) (PreH29 : ((os_sched_locks (history_final)) = 0)),
  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_task_current_ready history_returned history_final ) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
.

Definition OS_Sched_partial_solve_wit_13 := OS_Sched_partial_solve_wit_13_pure -> OS_Sched_partial_solve_wit_13_aux.

Definition OS_Sched_partial_solve_wit_14_pure :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (os_sched_task_current_ready history_returned history_final )) (PreH8 : ((os_sched_ints (history_final)) = 0)) (PreH9 : ((os_sched_locks (history_final)) = 0)) (PreH10 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH11 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH12 : (task_idle_ready sg (TskState (history_final)) )) (PreH13 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH18 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH19 : (os_sched_active_local_stable active )) (PreH20 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH21 : (kernel_call_task_source history_scheduled history_entry )) (PreH22 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH23 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH24 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH25 : (interrupt_saved_value mask cpu_sr )) (PreH26 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH27 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH28 : (UCOS2_state_inv sg history_final )) (PreH29 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH30 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH31 : ((os_sched_ints (history_final)) = 0)) (PreH32 : ((os_sched_locks (history_final)) = 0)),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (cpu_sr = cpu_sr) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (history_returned)) history_final ) ”
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH4 : (task_idle_ready sg (TskState (history_final)) )) (PreH5 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH6 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH7 : (task_idle_ready sg (TskState (history_final)) )) (PreH8 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH9 : (os_sched_task_current_ready history_returned history_final )) (PreH10 : ((os_sched_ints (history_final)) = 0)) (PreH11 : ((os_sched_locks (history_final)) = 0)) (PreH12 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH13 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH14 : (task_idle_ready sg (TskState (history_final)) )) (PreH15 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH18 : (kernel_sched_ready_clients critical )) (PreH19 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH20 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH21 : (os_sched_active_local_stable active )) (PreH22 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH23 : (kernel_call_task_source history_scheduled history_entry )) (PreH24 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH25 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH26 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH27 : (interrupt_saved_value mask cpu_sr )) (PreH28 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH29 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH30 : (UCOS2_state_inv sg history_final )) (PreH31 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH32 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH33 : ((os_sched_ints (history_final)) = 0)) (PreH34 : ((os_sched_locks (history_final)) = 0)),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
|--
  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (history_returned)) history_final ) ”
).

Definition OS_Sched_partial_solve_wit_14_pure_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH4 : (task_idle_ready sg (TskState (history_final)) )) (PreH5 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH6 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH7 : (task_idle_ready sg (TskState (history_final)) )) (PreH8 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH9 : (os_sched_task_current_ready history_returned history_final )) (PreH10 : ((os_sched_ints (history_final)) = 0)) (PreH11 : ((os_sched_locks (history_final)) = 0)) (PreH12 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH13 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH14 : (task_idle_ready sg (TskState (history_final)) )) (PreH15 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH18 : (kernel_sched_ready_clients critical )) (PreH19 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH20 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH21 : (os_sched_active_local_stable active )) (PreH22 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH23 : (kernel_call_task_source history_scheduled history_entry )) (PreH24 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH25 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH26 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH27 : (interrupt_saved_value mask cpu_sr )) (PreH28 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH29 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH30 : (UCOS2_state_inv sg history_final )) (PreH31 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH32 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH33 : ((os_sched_ints (history_final)) = 0)) (PreH34 : ((os_sched_locks (history_final)) = 0)),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
|--
  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (history_returned)) history_final ) ”
.

Definition OS_Sched_partial_solve_wit_14_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (os_sched_task_current_ready history_returned history_final )) (PreH8 : ((os_sched_ints (history_final)) = 0)) (PreH9 : ((os_sched_locks (history_final)) = 0)) (PreH10 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH11 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH12 : (task_idle_ready sg (TskState (history_final)) )) (PreH13 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH18 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH19 : (os_sched_active_local_stable active )) (PreH20 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH21 : (kernel_call_task_source history_scheduled history_entry )) (PreH22 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH23 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH24 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH25 : (interrupt_saved_value mask cpu_sr )) (PreH26 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH27 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH28 : (UCOS2_state_inv sg history_final )) (PreH29 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH30 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH31 : ((os_sched_ints (history_final)) = 0)) (PreH32 : ((os_sched_locks (history_final)) = 0)),
  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (cpu_sr = cpu_sr) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_caller_counters_zero active (FlagPendTaskCaller (history_returned)) history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_task_current_ready history_returned history_final ) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
.

Definition OS_Sched_partial_solve_wit_14 := OS_Sched_partial_solve_wit_14_pure -> OS_Sched_partial_solve_wit_14_aux.

Definition OS_Sched_partial_solve_wit_15_pure :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (os_sched_task_current_ready history_returned history_final )) (PreH8 : ((os_sched_ints (history_final)) = 0)) (PreH9 : ((os_sched_locks (history_final)) = 0)) (PreH10 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH11 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH12 : (task_idle_ready sg (TskState (history_final)) )) (PreH13 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH18 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH19 : (os_sched_active_local_stable active )) (PreH20 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH21 : (kernel_call_task_source history_scheduled history_entry )) (PreH22 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH23 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH24 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH25 : (interrupt_saved_value mask cpu_sr )) (PreH26 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH27 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH28 : (UCOS2_state_inv sg history_final )) (PreH29 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH30 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH31 : ((os_sched_ints (history_final)) = 0)) (PreH32 : ((os_sched_locks (history_final)) = 0)),
  (FlagPendActiveCaller.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
.

Definition OS_Sched_partial_solve_wit_15_aux :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH5 : (task_idle_ready sg (TskState (history_final)) )) (PreH6 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH7 : (os_sched_task_current_ready history_returned history_final )) (PreH8 : ((os_sched_ints (history_final)) = 0)) (PreH9 : ((os_sched_locks (history_final)) = 0)) (PreH10 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )) (PreH11 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH12 : (task_idle_ready sg (TskState (history_final)) )) (PreH13 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH18 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH19 : (os_sched_active_local_stable active )) (PreH20 : (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH21 : (kernel_call_task_source history_scheduled history_entry )) (PreH22 : (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final )) (PreH23 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH24 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH25 : (interrupt_saved_value mask cpu_sr )) (PreH26 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH27 : (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH28 : (UCOS2_state_inv sg history_final )) (PreH29 : (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry )) (PreH30 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH31 : ((os_sched_ints (history_final)) = 0)) (PreH32 : ((os_sched_locks (history_final)) = 0)),
  (FlagPendActiveCaller.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_task_current_ready history_returned history_final ) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_save_observation (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ (kernel_call_task_source history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_observation (task_sw_hook_call_environment (environment)) critical sg history_scheduled history_entry history_returned history_final ) ”
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ”
  &&  “ (SchedulerPhaseCandidate.os_sched_task_body_source (task_sw_hook_call_environment (environment)) critical sg history_entry history_scheduled history_returned history_final ) ”
  &&  “ (UCOS2_state_inv sg history_final ) ”
  &&  “ (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect (task_sw_hook_call_environment (environment)) critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (history_final)))) = true) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  (FlagPendActiveCaller.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
.

Definition OS_Sched_partial_solve_wit_15 := OS_Sched_partial_solve_wit_15_pure -> OS_Sched_partial_solve_wit_15_aux.

Definition OS_Sched_which_implies_wit_1 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before ) ”
  &&  “ (task_idle_ready sg (TskState (before)) ) ”
  &&  “ (flag_pend_non_idle_at sg context before ) ”
  &&  “ ((SchedStateDef.isRunning ((SchedState (before)))) = true) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (FlagPendActiveProtocol.flag_pend_active_protocol sg active ) ”
  &&  “ (FlagPendActiveCallerControl.flag_pend_active_requires_control active ) ”
  &&  “ (os_sched_active_local_stable active ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ (kernel_call_task_source context before ) ”
  &&  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
  &&  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_which_implies_wit_1_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_2 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ ((os_sched_locks (before)) = 0) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_3 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ ((os_sched_ints (before)) = 0) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_4 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (kernel_call_task_source context before ) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_5 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  “ (SchedulerCalleePhaseComponent.os_sched_task_entry_observation context before ) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_spatial :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH7 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH8 : (os_sched_active_local_stable active )) (PreH9 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (SchedulerCalleePhaseComponent.os_sched_task_call_pre (task_sw_hook_call_environment (environment)) local active sg context mask before )
|--
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_which_implies_wit_2 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : ((os_sched_ints (before)) = 0)) (PreH3 : ((os_sched_locks (before)) = 0)) (PreH4 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_call_cut sg context before ) ”
  &&  “ (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical ) ”
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  “ ((os_sched_locks (before)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active before ) ”
  &&  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : ((os_sched_ints (before)) = 0)) (PreH3 : ((os_sched_locks (before)) = 0)) (PreH4 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  “ (kernel_sched_ready_clients critical ) ”
  &&  “ (os_sched_call_cut sg context before ) ”
  &&  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
).

Definition OS_Sched_which_implies_wit_2_split_goal_1 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : ((os_sched_ints (before)) = 0)) (PreH3 : ((os_sched_locks (before)) = 0)) (PreH4 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  “ (kernel_sched_ready_clients critical ) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_2 :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : ((os_sched_ints (before)) = 0)) (PreH3 : ((os_sched_locks (before)) = 0)) (PreH4 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_call_cut sg context before ) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_spatial :=
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : ((os_sched_ints (before)) = 0)) (PreH3 : ((os_sched_locks (before)) = 0)) (PreH4 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (os_sched_active_save_input (task_sw_hook_call_environment (environment)) critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
.

Definition OS_Sched_which_implies_wit_3 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((os_sched_ints (before)) = 0)) (PreH2 : ((os_sched_locks (before)) = 0)) (PreH3 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
|--
  EX (entry_heap: model),
  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((os_sched_ints (before)) = 0)) (PreH2 : ((os_sched_locks (before)) = 0)) (PreH3 : (FlagPendEntryControl.flag_pend_active_entry sg active before )),
  (flag_pend_caller_save_input (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before )
|--
  EX (entry_heap: model),
  (os_sched_active_heap_cut (flag_pend_caller_save_input ((task_sw_hook_call_environment (environment))) (critical) (local) (active) (sg) ((FlagPendTaskCaller (context))) (context) (mask) (before)) entry_heap )
).

Definition OS_Sched_which_implies_wit_4 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (kernel_call_task_source context before )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((os_sched_ints (before)) = 0)) (PreH7 : ((os_sched_locks (before)) = 0)) (PreH8 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (FlagPendActiveCaller.flag_pend_selected_caller_save_output (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before entry_heap cpu_sr )
|--
  EX (save_caller: FlagPendCaller) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (cpu_sr) (save_entry) (save_entry)) save_after_heap )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (context)) before )) (PreH2 : (task_idle_ready sg (TskState (before)) )) (PreH3 : (flag_pend_non_idle_at sg context before )) (PreH4 : (kernel_call_task_source context before )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((os_sched_ints (before)) = 0)) (PreH7 : ((os_sched_locks (before)) = 0)) (PreH8 : ((SchedStateDef.isRunning ((SchedState (before)))) = true)),
  (FlagPendActiveCaller.flag_pend_selected_caller_save_output (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask before entry_heap cpu_sr )
|--
  EX (save_caller: FlagPendCaller) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (cpu_sr) (save_entry) (save_entry)) save_after_heap )
).

Definition OS_Sched_which_implies_wit_5 :=
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (kernel_tcb_stack_field_layout sg )) (PreH5 : (kernel_call_task_source context before )) (PreH6 : (kernel_call_stack_available context before )) (PreH7 : (task_idle_ready sg (TskState (before)) )) (PreH8 : (os_sched_call_cut sg context before )) (PreH9 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )),
  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (cpu_sr) (save_entry) (save_entry)) save_after_heap )
|--
  EX (active_before: model),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  “ (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before ) ”
  &&  “ (kernel_call_normal_return context before save_scheduled save_entry ) ”
  &&  “ (kernel_call_control_rely sg before save_entry ) ”
  &&  “ (kernel_call_task_source save_scheduled save_entry ) ”
  &&  “ (os_sched_call_cut sg save_scheduled save_entry ) ”
  &&  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask cpu_sr before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry_heap: model) (save_caller: FlagPendCaller) (save_scheduled: OsSchedCallContext) (save_entry: UCOS2_Verify_State) (save_local: (Armv7aContinuation -> Assertion)) (save_after_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry )) (PreH2 : (task_idle_ready sg (TskState (save_entry)) )) (PreH3 : (flag_pend_non_idle_at sg save_scheduled save_entry )) (PreH4 : (kernel_tcb_stack_field_layout sg )) (PreH5 : (kernel_call_task_source context before )) (PreH6 : (kernel_call_stack_available context before )) (PreH7 : (task_idle_ready sg (TskState (before)) )) (PreH8 : (os_sched_call_cut sg context before )) (PreH9 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap )),
  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (save_local) (active) (sg) (save_caller) (save_scheduled) (cpu_sr) (save_entry) (save_entry)) save_after_heap )
|--
  EX (active_before: model),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (save_scheduled)) save_entry ) ”
  &&  “ (task_idle_ready sg (TskState (save_entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg save_scheduled save_entry ) ”
  &&  “ (SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event (task_sw_hook_call_environment (environment)) critical local active sg (FlagPendTaskCaller (context)) context mask cpu_sr before save_caller save_scheduled save_entry save_local entry_heap save_after_heap ) ”
  &&  “ (SchedulerPairedPhaseComponent.os_sched_paired_save_entry_heap (task_sw_hook_call_environment (environment)) critical local active sg context mask before entry_heap active_before ) ”
  &&  “ (kernel_call_normal_return context before save_scheduled save_entry ) ”
  &&  “ (kernel_call_control_rely sg before save_entry ) ”
  &&  “ (kernel_call_task_source save_scheduled save_entry ) ”
  &&  “ (os_sched_call_cut sg save_scheduled save_entry ) ”
  &&  (SchedulerActivePhaseComponent.os_sched_active_save_event (task_sw_hook_call_environment (environment)) critical local active sg context mask cpu_sr before save_scheduled save_entry save_local active_before )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_which_implies_wit_6 :=
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )),
  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
|--
  EX (switch_heap: model),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH2 : (task_idle_ready sg (TskState (entry)) )) (PreH3 : (flag_pend_non_idle_at sg scheduled entry )),
  (SchedulerCalleePhaseComponent.os_sched_task_switch_pre (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry )
|--
  EX (switch_heap: model),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry ) ”
  &&  “ (task_idle_ready sg (TskState (entry)) ) ”
  &&  “ (flag_pend_non_idle_at sg scheduled entry ) ”
  &&  (os_sched_active_heap_cut (SchedulerCalleePhaseComponent.os_sched_task_switch_pre ((task_sw_hook_call_environment (environment))) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
).

Definition OS_Sched_which_implies_wit_7 :=
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH3 : (task_idle_ready sg (TskState (entry)) )) (PreH4 : (flag_pend_non_idle_at sg scheduled entry )),
  (tmr_task_sched_switch_source_post (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  (tmr_task_sched_switch_entry_output (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH3 : (task_idle_ready sg (TskState (entry)) )) (PreH4 : (flag_pend_non_idle_at sg scheduled entry )),
  (tmr_task_sched_switch_source_post (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  (tmr_task_sched_switch_entry_output (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
).

Definition OS_Sched_which_implies_wit_7_split_goal_spatial :=
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_registered_source_coverage (task_stack_call_external (environment)) critical )) (PreH2 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (scheduled)) entry )) (PreH3 : (task_idle_ready sg (TskState (entry)) )) (PreH4 : (flag_pend_non_idle_at sg scheduled entry )),
  (tmr_task_sched_switch_source_post (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  (tmr_task_sched_switch_entry_output (task_sw_hook_call_environment (environment)) critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
.

Definition OS_Sched_which_implies_wit_8 :=
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH7 : ((os_sched_ints (history_final)) = 0)) (PreH8 : ((os_sched_locks (history_final)) = 0)),
  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  “ (os_sched_task_current_ready history_returned history_final ) ”
  &&  “ ((os_sched_ints (history_final)) = 0) ”
  &&  “ ((os_sched_locks (history_final)) = 0) ”
  &&  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH7 : ((os_sched_ints (history_final)) = 0)) (PreH8 : ((os_sched_locks (history_final)) = 0)),
  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
  &&  “ (os_sched_task_current_ready history_returned history_final ) ”
  &&  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
).

Definition OS_Sched_which_implies_wit_8_split_goal_1 :=
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH7 : ((os_sched_ints (history_final)) = 0)) (PreH8 : ((os_sched_locks (history_final)) = 0)),
  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (FlagPendEntryControl.flag_pend_active_entry sg active history_final ) ”
.

Definition OS_Sched_which_implies_wit_8_split_goal_2 :=
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH7 : ((os_sched_ints (history_final)) = 0)) (PreH8 : ((os_sched_locks (history_final)) = 0)),
  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_task_current_ready history_returned history_final ) ”
.

Definition OS_Sched_which_implies_wit_8_split_goal_spatial :=
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveProtocol.flag_pend_active_protocol sg active )) (PreH5 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )) (PreH6 : ((SchedStateDef.isRunning ((SchedState (history_final)))) = true)) (PreH7 : ((os_sched_ints (history_final)) = 0)) (PreH8 : ((os_sched_locks (history_final)) = 0)),
  (SchedulerCalleePhaseComponent.os_sched_task_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
.

Definition OS_Sched_which_implies_wit_9 :=
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : ((os_sched_ints (history_final)) = 0)) (PreH5 : ((os_sched_locks (history_final)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )),
  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
|--
  EX (restore_heap: model),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : ((os_sched_ints (history_final)) = 0)) (PreH5 : ((os_sched_locks (history_final)) = 0)) (PreH6 : (FlagPendEntryControl.flag_pend_active_entry sg active history_final )),
  (flag_pend_caller_restore_input (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final )
|--
  EX (restore_heap: model),
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  (os_sched_active_heap_cut (flag_pend_caller_restore_input ((task_sw_hook_call_environment (environment))) (critical) (history_local) (active) (sg) ((FlagPendTaskCaller (history_returned))) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
).

Definition OS_Sched_which_implies_wit_10 :=
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )),
  (FlagPendActiveCaller.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  “ (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final ) ”
  &&  “ (task_idle_ready sg (TskState (history_final)) ) ”
  &&  “ (flag_pend_non_idle_at sg history_returned history_final ) ”
  &&  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )),
  (FlagPendActiveCaller.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
).

Definition OS_Sched_which_implies_wit_10_split_goal_spatial :=
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (cpu_sr: Z) (PreH1 : (tmr_task_signal_lifetime critical sg (os_sched_call_invocation (history_returned)) history_final )) (PreH2 : (task_idle_ready sg (TskState (history_final)) )) (PreH3 : (flag_pend_non_idle_at sg history_returned history_final )) (PreH4 : (FlagPendActiveCallerControl.flag_pend_active_requires_control active )),
  (FlagPendActiveCaller.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
|--
  (SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output (task_sw_hook_call_environment (environment)) critical history_local active sg (FlagPendTaskCaller (history_returned)) history_returned cpu_sr history_entry history_final restore_heap )
.

Module Type VC_Correct.


Axiom proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Axiom proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Axiom proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Axiom proof_of_OS_Sched_entail_wit_2 : OS_Sched_entail_wit_2.
Axiom proof_of_OS_Sched_entail_wit_3 : OS_Sched_entail_wit_3.
Axiom proof_of_OS_Sched_entail_wit_4_1 : OS_Sched_entail_wit_4_1.
Axiom proof_of_OS_Sched_entail_wit_4_2 : OS_Sched_entail_wit_4_2.
Axiom proof_of_OS_Sched_entail_wit_4_3 : OS_Sched_entail_wit_4_3.
Axiom proof_of_OS_Sched_entail_wit_4_4 : OS_Sched_entail_wit_4_4.
Axiom proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_1_pure : OS_Sched_partial_solve_wit_1_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_2_pure : OS_Sched_partial_solve_wit_2_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Axiom proof_of_OS_Sched_partial_solve_wit_3_pure : OS_Sched_partial_solve_wit_3_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Axiom proof_of_OS_Sched_partial_solve_wit_4_pure : OS_Sched_partial_solve_wit_4_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Axiom proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Axiom proof_of_OS_Sched_partial_solve_wit_6_pure : OS_Sched_partial_solve_wit_6_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_6 : OS_Sched_partial_solve_wit_6.
Axiom proof_of_OS_Sched_partial_solve_wit_7_pure : OS_Sched_partial_solve_wit_7_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_7 : OS_Sched_partial_solve_wit_7.
Axiom proof_of_OS_Sched_partial_solve_wit_8 : OS_Sched_partial_solve_wit_8.
Axiom proof_of_OS_Sched_partial_solve_wit_9_pure : OS_Sched_partial_solve_wit_9_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_9 : OS_Sched_partial_solve_wit_9.
Axiom proof_of_OS_Sched_partial_solve_wit_10_pure : OS_Sched_partial_solve_wit_10_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_10 : OS_Sched_partial_solve_wit_10.
Axiom proof_of_OS_Sched_partial_solve_wit_11_pure : OS_Sched_partial_solve_wit_11_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_11 : OS_Sched_partial_solve_wit_11.
Axiom proof_of_OS_Sched_partial_solve_wit_12_pure : OS_Sched_partial_solve_wit_12_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_12 : OS_Sched_partial_solve_wit_12.
Axiom proof_of_OS_Sched_partial_solve_wit_13_pure : OS_Sched_partial_solve_wit_13_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_13 : OS_Sched_partial_solve_wit_13.
Axiom proof_of_OS_Sched_partial_solve_wit_14_pure : OS_Sched_partial_solve_wit_14_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_14 : OS_Sched_partial_solve_wit_14.
Axiom proof_of_OS_Sched_partial_solve_wit_15_pure : OS_Sched_partial_solve_wit_15_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_15 : OS_Sched_partial_solve_wit_15.
Axiom proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Axiom proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Axiom proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.
Axiom proof_of_OS_Sched_which_implies_wit_4 : OS_Sched_which_implies_wit_4.
Axiom proof_of_OS_Sched_which_implies_wit_5 : OS_Sched_which_implies_wit_5.
Axiom proof_of_OS_Sched_which_implies_wit_6 : OS_Sched_which_implies_wit_6.
Axiom proof_of_OS_Sched_which_implies_wit_7 : OS_Sched_which_implies_wit_7.
Axiom proof_of_OS_Sched_which_implies_wit_8 : OS_Sched_which_implies_wit_8.
Axiom proof_of_OS_Sched_which_implies_wit_9 : OS_Sched_which_implies_wit_9.
Axiom proof_of_OS_Sched_which_implies_wit_10 : OS_Sched_which_implies_wit_10.

End VC_Correct.
