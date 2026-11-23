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
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_begin_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_tcb_list_selected_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Require Import Ucos2Verify.VC.code.memory.spec.mem_init_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_generic_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_stat_continuation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_end_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_debug_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSInit -----*)

Definition OSInit_return_wit_1 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_return_stage p idle stat timer X )
|--
  (os_init_post p X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_return_stage p idle stat timer X )
|--
  (os_init_post p X )
).

Definition OSInit_return_wit_1_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_return_stage p idle stat timer X )
|--
  (os_init_post p X )
.

Definition OSInit_partial_solve_wit_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_pre p X )
|--
  (os_init_pre p X )
.

Definition OSInit_partial_solve_wit_2_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_hook_port_pre ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_exception_initial (p)) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OS_CPU_ExceptStk" ) ) = ( &( "OS_CPU_ExceptStk" ) )) ”
.

Definition OSInit_partial_solve_wit_2_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_hook_port_pre ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_exception_initial (p)) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OS_CPU_ExceptStk" ) ) = ( &( "OS_CPU_ExceptStk" ) )) ”
  &&  (os_init_hook_port_pre ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_exception_initial (p)) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_partial_solve_wit_2 := OSInit_partial_solve_wit_2_pure -> OSInit_partial_solve_wit_2_aux.

Definition OSInit_partial_solve_wit_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OS_CPU_ExceptStk" ) ) = ( &( "OS_CPU_ExceptStk" ) ))) ,
  (os_init_hook_port_post ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_hook_port_post ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_partial_solve_wit_4 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S (O)) X )
|--
  (os_init_raw_stage p (S (O)) X )
.

Definition OSInit_partial_solve_wit_5_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  ((( &( "OSTime" ) )) # UInt  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |->_)
  **  ((( &( "OSLockNesting" ) )) # UChar  |->_)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |->_)
  **  ((( &( "OSRunning" ) )) # UChar  |->_)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |->_)
  **  ((( &( "OSStatRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |->_)
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
.

Definition OSInit_partial_solve_wit_5_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  ((( &( "OSTime" ) )) # UInt  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |->_)
  **  ((( &( "OSLockNesting" ) )) # UChar  |->_)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |->_)
  **  ((( &( "OSRunning" ) )) # UChar  |->_)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |->_)
  **  ((( &( "OSStatRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |->_)
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  ((( &( "OSTime" ) )) # UInt  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |->_)
  **  ((( &( "OSLockNesting" ) )) # UChar  |->_)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |->_)
  **  ((( &( "OSRunning" ) )) # UChar  |->_)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |->_)
  **  ((( &( "OSStatRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |->_)
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_partial_solve_wit_5 := OSInit_partial_solve_wit_5_pure -> OSInit_partial_solve_wit_5_aux.

Definition OSInit_partial_solve_wit_6 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_misc_zero (os_init_sg (p)) )
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_misc_zero (os_init_sg (p)) )
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_partial_solve_wit_7 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S (O)))) X )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S (O)))) X )
.

Definition OSInit_partial_solve_wit_8 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_partial_solve_wit_9 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_partial_solve_wit_10 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S ((S (O)))))) X )
.

Definition OSInit_partial_solve_wit_11_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH2 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH4 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH5 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH6 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH7 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH9 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH10 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH11 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH12 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH13 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH14 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_tcb_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ”
.

Definition OSInit_partial_solve_wit_11_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH2 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH4 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH5 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH6 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH7 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH8 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH9 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH10 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH11 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH12 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH13 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH14 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_tcb_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_tcb_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
.

Definition OSInit_partial_solve_wit_11 := OSInit_partial_solve_wit_11_pure -> OSInit_partial_solve_wit_11_aux.

Definition OSInit_partial_solve_wit_12 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH2 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH4 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH5 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH7 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH9 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH10 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH11 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH12 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH13 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH14 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH15 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH16 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH17 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_tcb_list_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_tcb_list_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
.

Definition OSInit_partial_solve_wit_13 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH2 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH4 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH5 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH7 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH8 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH9 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH10 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH11 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH12 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH13 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH14 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH15 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH16 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH17 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
.

Definition OSInit_partial_solve_wit_14_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH2 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 20)) (PreH5 : ((sizeof( "os_event" ) * 10) = 200)) (PreH6 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH7 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH9 : (event_table_layout_prop (os_init_sg (p)) )) (PreH10 : (init_event_list_profile (os_init_sg (p)) )) (PreH11 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH12 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH14 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH15 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH16 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH17 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH19 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH20 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH21 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH22 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH23 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH24 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH25 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH26 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH27 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_event_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ”
.

Definition OSInit_partial_solve_wit_14_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH2 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 20)) (PreH5 : ((sizeof( "os_event" ) * 10) = 200)) (PreH6 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH7 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH9 : (event_table_layout_prop (os_init_sg (p)) )) (PreH10 : (init_event_list_profile (os_init_sg (p)) )) (PreH11 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH12 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH14 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH15 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH16 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH17 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH18 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH19 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH20 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH21 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH22 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH23 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH24 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH25 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH26 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH27 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_event_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_event_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
.

Definition OSInit_partial_solve_wit_14 := OSInit_partial_solve_wit_14_pure -> OSInit_partial_solve_wit_14_aux.

Definition OSInit_partial_solve_wit_15 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH2 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 20)) (PreH5 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH6 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH8 : (event_table_layout_prop (os_init_sg (p)) )) (PreH9 : (init_event_list_profile (os_init_sg (p)) )) (PreH10 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH11 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH12 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH13 : (sizeof( "os_event" ) = 20)) (PreH14 : ((sizeof( "os_event" ) * 10) = 200)) (PreH15 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH16 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH17 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH18 : (event_table_layout_prop (os_init_sg (p)) )) (PreH19 : (init_event_list_profile (os_init_sg (p)) )) (PreH20 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH21 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH22 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH23 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH24 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH25 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH26 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH27 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH28 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH29 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH30 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH31 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH32 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH33 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH34 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH35 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH36 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_event_list_post (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_event_list_post (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
.

Definition OSInit_partial_solve_wit_16 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH2 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 20)) (PreH5 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH6 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH8 : (event_table_layout_prop (os_init_sg (p)) )) (PreH9 : (init_event_list_profile (os_init_sg (p)) )) (PreH10 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH11 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH12 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH13 : (sizeof( "os_event" ) = 20)) (PreH14 : ((sizeof( "os_event" ) * 10) = 200)) (PreH15 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH16 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH17 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH18 : (event_table_layout_prop (os_init_sg (p)) )) (PreH19 : (init_event_list_profile (os_init_sg (p)) )) (PreH20 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH21 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH22 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH23 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH24 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH25 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH26 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH27 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH28 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH29 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH30 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH31 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH32 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH33 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH34 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH35 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH36 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
.

Definition OSInit_partial_solve_wit_17_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (flag_init_profile (os_init_sg (p)) )) (PreH2 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH6 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 20)) (PreH9 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH10 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH11 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH12 : (event_table_layout_prop (os_init_sg (p)) )) (PreH13 : (init_event_list_profile (os_init_sg (p)) )) (PreH14 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH15 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH16 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH17 : (sizeof( "os_event" ) = 20)) (PreH18 : ((sizeof( "os_event" ) * 10) = 200)) (PreH19 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH20 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH21 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH22 : (event_table_layout_prop (os_init_sg (p)) )) (PreH23 : (init_event_list_profile (os_init_sg (p)) )) (PreH24 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH25 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH26 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH27 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH28 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH29 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH30 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH32 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH33 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH34 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH35 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH36 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH37 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH38 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH39 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH40 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (flag_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
.

Definition OSInit_partial_solve_wit_17_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (flag_init_profile (os_init_sg (p)) )) (PreH2 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH6 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 20)) (PreH9 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH10 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH11 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH12 : (event_table_layout_prop (os_init_sg (p)) )) (PreH13 : (init_event_list_profile (os_init_sg (p)) )) (PreH14 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH15 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH16 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH17 : (sizeof( "os_event" ) = 20)) (PreH18 : ((sizeof( "os_event" ) * 10) = 200)) (PreH19 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH20 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH21 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH22 : (event_table_layout_prop (os_init_sg (p)) )) (PreH23 : (init_event_list_profile (os_init_sg (p)) )) (PreH24 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH25 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH26 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH27 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH28 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH29 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH30 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH31 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH32 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH33 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH34 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH35 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH36 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH37 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH38 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH39 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH40 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (flag_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (flag_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
.

Definition OSInit_partial_solve_wit_17 := OSInit_partial_solve_wit_17_pure -> OSInit_partial_solve_wit_17_aux.

Definition OSInit_partial_solve_wit_18 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (flag_init_profile (os_init_sg (p)) )) (PreH2 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile (os_init_sg (p)) )) (PreH6 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout (os_init_sg (p)) )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH9 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH10 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH11 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH12 : (sizeof( "os_event" ) = 20)) (PreH13 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH14 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH15 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH16 : (event_table_layout_prop (os_init_sg (p)) )) (PreH17 : (init_event_list_profile (os_init_sg (p)) )) (PreH18 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH19 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH20 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH21 : (sizeof( "os_event" ) = 20)) (PreH22 : ((sizeof( "os_event" ) * 10) = 200)) (PreH23 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH24 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH25 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH26 : (event_table_layout_prop (os_init_sg (p)) )) (PreH27 : (init_event_list_profile (os_init_sg (p)) )) (PreH28 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH29 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH30 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH31 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH32 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH33 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH34 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH36 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH37 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH38 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH39 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH40 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH41 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH42 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH43 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH44 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (flag_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (flag_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
.

Definition OSInit_partial_solve_wit_19 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (flag_init_profile (os_init_sg (p)) )) (PreH2 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile (os_init_sg (p)) )) (PreH6 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout (os_init_sg (p)) )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH9 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH10 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH11 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH12 : (sizeof( "os_event" ) = 20)) (PreH13 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH14 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH15 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH16 : (event_table_layout_prop (os_init_sg (p)) )) (PreH17 : (init_event_list_profile (os_init_sg (p)) )) (PreH18 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH19 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH20 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH21 : (sizeof( "os_event" ) = 20)) (PreH22 : ((sizeof( "os_event" ) * 10) = 200)) (PreH23 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH24 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH25 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH26 : (event_table_layout_prop (os_init_sg (p)) )) (PreH27 : (init_event_list_profile (os_init_sg (p)) )) (PreH28 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH29 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH30 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH31 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH32 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH33 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH34 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH35 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH36 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH37 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH38 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH39 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH40 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH41 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH42 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH43 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH44 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
.

Definition OSInit_partial_solve_wit_20_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (mem_init_profile (os_init_sg (p)) )) (PreH2 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (flag_init_profile (os_init_sg (p)) )) (PreH6 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout (os_init_sg (p)) )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH9 : (flag_init_profile (os_init_sg (p)) )) (PreH10 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_init_layout (os_init_sg (p)) )) (PreH12 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH13 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH14 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH15 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH16 : (sizeof( "os_event" ) = 20)) (PreH17 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH18 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH19 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH20 : (event_table_layout_prop (os_init_sg (p)) )) (PreH21 : (init_event_list_profile (os_init_sg (p)) )) (PreH22 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH23 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH24 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH25 : (sizeof( "os_event" ) = 20)) (PreH26 : ((sizeof( "os_event" ) * 10) = 200)) (PreH27 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH28 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH29 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH30 : (event_table_layout_prop (os_init_sg (p)) )) (PreH31 : (init_event_list_profile (os_init_sg (p)) )) (PreH32 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH33 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH34 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH35 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH36 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH37 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH38 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH39 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH40 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH41 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH42 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH43 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH44 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH45 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH46 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH47 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH48 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (mem_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
.

Definition OSInit_partial_solve_wit_20_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (mem_init_profile (os_init_sg (p)) )) (PreH2 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (flag_init_profile (os_init_sg (p)) )) (PreH6 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout (os_init_sg (p)) )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH9 : (flag_init_profile (os_init_sg (p)) )) (PreH10 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_init_layout (os_init_sg (p)) )) (PreH12 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH13 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH14 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH15 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH16 : (sizeof( "os_event" ) = 20)) (PreH17 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH18 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH19 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH20 : (event_table_layout_prop (os_init_sg (p)) )) (PreH21 : (init_event_list_profile (os_init_sg (p)) )) (PreH22 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH23 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH24 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH25 : (sizeof( "os_event" ) = 20)) (PreH26 : ((sizeof( "os_event" ) * 10) = 200)) (PreH27 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH28 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH29 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH30 : (event_table_layout_prop (os_init_sg (p)) )) (PreH31 : (init_event_list_profile (os_init_sg (p)) )) (PreH32 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH33 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH34 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH35 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH36 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH37 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH38 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH39 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH40 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH41 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH42 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH43 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH44 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH45 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH46 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH47 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH48 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (mem_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (mem_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
.

Definition OSInit_partial_solve_wit_20 := OSInit_partial_solve_wit_20_pure -> OSInit_partial_solve_wit_20_aux.

Definition OSInit_partial_solve_wit_21 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (mem_init_profile (os_init_sg (p)) )) (PreH2 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile (os_init_sg (p)) )) (PreH6 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout (os_init_sg (p)) )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH9 : (flag_init_profile (os_init_sg (p)) )) (PreH10 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_init_layout (os_init_sg (p)) )) (PreH12 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH13 : (flag_init_profile (os_init_sg (p)) )) (PreH14 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH15 : (flag_init_layout (os_init_sg (p)) )) (PreH16 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH17 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH18 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH19 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH20 : (sizeof( "os_event" ) = 20)) (PreH21 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH22 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH23 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH24 : (event_table_layout_prop (os_init_sg (p)) )) (PreH25 : (init_event_list_profile (os_init_sg (p)) )) (PreH26 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH27 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH28 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH29 : (sizeof( "os_event" ) = 20)) (PreH30 : ((sizeof( "os_event" ) * 10) = 200)) (PreH31 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH32 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH33 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH34 : (event_table_layout_prop (os_init_sg (p)) )) (PreH35 : (init_event_list_profile (os_init_sg (p)) )) (PreH36 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH37 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH38 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH39 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH40 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH41 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH42 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH43 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH44 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH45 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH46 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH47 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH48 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH49 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH50 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH51 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH52 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (mem_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (mem_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
.

Definition OSInit_partial_solve_wit_22 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (mem_init_profile (os_init_sg (p)) )) (PreH2 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout (os_init_sg (p)) )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile (os_init_sg (p)) )) (PreH6 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout (os_init_sg (p)) )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH9 : (flag_init_profile (os_init_sg (p)) )) (PreH10 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH11 : (flag_init_layout (os_init_sg (p)) )) (PreH12 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH13 : (flag_init_profile (os_init_sg (p)) )) (PreH14 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH15 : (flag_init_layout (os_init_sg (p)) )) (PreH16 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH17 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH18 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH19 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH20 : (sizeof( "os_event" ) = 20)) (PreH21 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH22 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH23 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH24 : (event_table_layout_prop (os_init_sg (p)) )) (PreH25 : (init_event_list_profile (os_init_sg (p)) )) (PreH26 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH27 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH28 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH29 : (sizeof( "os_event" ) = 20)) (PreH30 : ((sizeof( "os_event" ) * 10) = 200)) (PreH31 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH32 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH33 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH34 : (event_table_layout_prop (os_init_sg (p)) )) (PreH35 : (init_event_list_profile (os_init_sg (p)) )) (PreH36 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH37 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH38 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH39 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH40 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH41 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH42 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH43 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH44 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH45 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH46 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH47 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH48 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH49 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH50 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH51 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH52 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
.

Definition OSInit_partial_solve_wit_23_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH2 : (queue_first_round_profile (os_init_sg (p)) )) (PreH3 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH6 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH7 : (mem_init_profile (os_init_sg (p)) )) (PreH8 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout (os_init_sg (p)) )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH11 : (mem_init_profile (os_init_sg (p)) )) (PreH12 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH13 : (mem_init_layout (os_init_sg (p)) )) (PreH14 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH15 : (flag_init_profile (os_init_sg (p)) )) (PreH16 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH17 : (flag_init_layout (os_init_sg (p)) )) (PreH18 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH19 : (flag_init_profile (os_init_sg (p)) )) (PreH20 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH21 : (flag_init_layout (os_init_sg (p)) )) (PreH22 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH23 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH24 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH25 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH26 : (sizeof( "os_event" ) = 20)) (PreH27 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH28 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH29 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH30 : (event_table_layout_prop (os_init_sg (p)) )) (PreH31 : (init_event_list_profile (os_init_sg (p)) )) (PreH32 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH33 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH34 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH35 : (sizeof( "os_event" ) = 20)) (PreH36 : ((sizeof( "os_event" ) * 10) = 200)) (PreH37 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH38 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH39 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH40 : (event_table_layout_prop (os_init_sg (p)) )) (PreH41 : (init_event_list_profile (os_init_sg (p)) )) (PreH42 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH43 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH44 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH45 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH46 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH47 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH48 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH49 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH50 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH51 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH52 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH53 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH54 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH55 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH56 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH57 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH58 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (queue_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ”
.

Definition OSInit_partial_solve_wit_23_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH2 : (queue_first_round_profile (os_init_sg (p)) )) (PreH3 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH6 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH7 : (mem_init_profile (os_init_sg (p)) )) (PreH8 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout (os_init_sg (p)) )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH11 : (mem_init_profile (os_init_sg (p)) )) (PreH12 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH13 : (mem_init_layout (os_init_sg (p)) )) (PreH14 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH15 : (flag_init_profile (os_init_sg (p)) )) (PreH16 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH17 : (flag_init_layout (os_init_sg (p)) )) (PreH18 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH19 : (flag_init_profile (os_init_sg (p)) )) (PreH20 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH21 : (flag_init_layout (os_init_sg (p)) )) (PreH22 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH23 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH24 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH25 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH26 : (sizeof( "os_event" ) = 20)) (PreH27 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH28 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH29 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH30 : (event_table_layout_prop (os_init_sg (p)) )) (PreH31 : (init_event_list_profile (os_init_sg (p)) )) (PreH32 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH33 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH34 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH35 : (sizeof( "os_event" ) = 20)) (PreH36 : ((sizeof( "os_event" ) * 10) = 200)) (PreH37 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH38 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH39 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH40 : (event_table_layout_prop (os_init_sg (p)) )) (PreH41 : (init_event_list_profile (os_init_sg (p)) )) (PreH42 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH43 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH44 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH45 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH46 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH47 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH48 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH49 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH50 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH51 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH52 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH53 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH54 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH55 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH56 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH57 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH58 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (queue_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (queue_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
.

Definition OSInit_partial_solve_wit_23 := OSInit_partial_solve_wit_23_pure -> OSInit_partial_solve_wit_23_aux.

Definition OSInit_partial_solve_wit_24 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH2 : (queue_first_round_profile (os_init_sg (p)) )) (PreH3 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH6 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH7 : (queue_first_round_profile (os_init_sg (p)) )) (PreH8 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH9 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH10 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH11 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH12 : (mem_init_profile (os_init_sg (p)) )) (PreH13 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH14 : (mem_init_layout (os_init_sg (p)) )) (PreH15 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH16 : (mem_init_profile (os_init_sg (p)) )) (PreH17 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH18 : (mem_init_layout (os_init_sg (p)) )) (PreH19 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH20 : (flag_init_profile (os_init_sg (p)) )) (PreH21 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : (flag_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH24 : (flag_init_profile (os_init_sg (p)) )) (PreH25 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH26 : (flag_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH28 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH29 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH30 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH31 : (sizeof( "os_event" ) = 20)) (PreH32 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH33 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH34 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH35 : (event_table_layout_prop (os_init_sg (p)) )) (PreH36 : (init_event_list_profile (os_init_sg (p)) )) (PreH37 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH38 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH39 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH40 : (sizeof( "os_event" ) = 20)) (PreH41 : ((sizeof( "os_event" ) * 10) = 200)) (PreH42 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH43 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH44 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH45 : (event_table_layout_prop (os_init_sg (p)) )) (PreH46 : (init_event_list_profile (os_init_sg (p)) )) (PreH47 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH48 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH49 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH50 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH51 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH52 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH53 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH54 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH55 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH56 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH57 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH58 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH59 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH60 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH61 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH62 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH63 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (OS_QInit_spec (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (OS_QInit_spec (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
.

Definition OSInit_partial_solve_wit_25 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH2 : (queue_first_round_profile (os_init_sg (p)) )) (PreH3 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH6 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH7 : (queue_first_round_profile (os_init_sg (p)) )) (PreH8 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH9 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH10 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH11 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH12 : (mem_init_profile (os_init_sg (p)) )) (PreH13 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH14 : (mem_init_layout (os_init_sg (p)) )) (PreH15 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH16 : (mem_init_profile (os_init_sg (p)) )) (PreH17 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH18 : (mem_init_layout (os_init_sg (p)) )) (PreH19 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH20 : (flag_init_profile (os_init_sg (p)) )) (PreH21 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : (flag_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH24 : (flag_init_profile (os_init_sg (p)) )) (PreH25 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH26 : (flag_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH28 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH29 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH30 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH31 : (sizeof( "os_event" ) = 20)) (PreH32 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH33 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH34 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH35 : (event_table_layout_prop (os_init_sg (p)) )) (PreH36 : (init_event_list_profile (os_init_sg (p)) )) (PreH37 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH38 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH39 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH40 : (sizeof( "os_event" ) = 20)) (PreH41 : ((sizeof( "os_event" ) * 10) = 200)) (PreH42 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH43 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH44 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH45 : (event_table_layout_prop (os_init_sg (p)) )) (PreH46 : (init_event_list_profile (os_init_sg (p)) )) (PreH47 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH48 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH49 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH50 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH51 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH52 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH53 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH54 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH55 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH56 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH57 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH58 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH59 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH60 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH61 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH62 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH63 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
.

Definition OSInit_partial_solve_wit_26 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH2 : (queue_first_round_profile (os_init_sg (p)) )) (PreH3 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH6 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH7 : (queue_first_round_profile (os_init_sg (p)) )) (PreH8 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH9 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH10 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH11 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH12 : (mem_init_profile (os_init_sg (p)) )) (PreH13 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH14 : (mem_init_layout (os_init_sg (p)) )) (PreH15 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH16 : (mem_init_profile (os_init_sg (p)) )) (PreH17 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH18 : (mem_init_layout (os_init_sg (p)) )) (PreH19 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH20 : (flag_init_profile (os_init_sg (p)) )) (PreH21 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH22 : (flag_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH24 : (flag_init_profile (os_init_sg (p)) )) (PreH25 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH26 : (flag_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH28 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH29 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH30 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH31 : (sizeof( "os_event" ) = 20)) (PreH32 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH33 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH34 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH35 : (event_table_layout_prop (os_init_sg (p)) )) (PreH36 : (init_event_list_profile (os_init_sg (p)) )) (PreH37 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH38 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH39 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH40 : (sizeof( "os_event" ) = 20)) (PreH41 : ((sizeof( "os_event" ) * 10) = 200)) (PreH42 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH43 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH44 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH45 : (event_table_layout_prop (os_init_sg (p)) )) (PreH46 : (init_event_list_profile (os_init_sg (p)) )) (PreH47 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH48 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH49 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH50 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH51 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH52 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH53 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH54 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH55 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH56 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH57 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH58 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH59 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH60 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH61 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH62 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH63 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_before_idle p X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_before_idle p X )
.

Definition OSInit_partial_solve_wit_27_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH7 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH8 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH9 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH10 : (queue_first_round_profile (os_init_sg (p)) )) (PreH11 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH14 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH15 : (queue_first_round_profile (os_init_sg (p)) )) (PreH16 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH17 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH18 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH19 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH20 : (mem_init_profile (os_init_sg (p)) )) (PreH21 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH22 : (mem_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH24 : (mem_init_profile (os_init_sg (p)) )) (PreH25 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH26 : (mem_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH28 : (flag_init_profile (os_init_sg (p)) )) (PreH29 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH32 : (flag_init_profile (os_init_sg (p)) )) (PreH33 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH34 : (flag_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH36 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH37 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH38 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH39 : (sizeof( "os_event" ) = 20)) (PreH40 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH41 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH42 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH43 : (event_table_layout_prop (os_init_sg (p)) )) (PreH44 : (init_event_list_profile (os_init_sg (p)) )) (PreH45 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH46 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH47 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH48 : (sizeof( "os_event" ) = 20)) (PreH49 : ((sizeof( "os_event" ) * 10) = 200)) (PreH50 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH51 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH52 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH53 : (event_table_layout_prop (os_init_sg (p)) )) (PreH54 : (init_event_list_profile (os_init_sg (p)) )) (PreH55 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH56 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH57 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH58 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH59 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH60 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH61 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH62 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH63 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH64 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH65 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH66 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH67 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH68 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH69 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH70 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH71 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_idle_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) )
  **  (os_init_idle_call_frame p )
|--
  “ (( &( "OS_TaskIdle" ) ) = ( &( "OS_TaskIdle" ) )) ” 
  &&  “ (( &( "OSTaskIdleStk" ) ) = ( &( "OSTaskIdleStk" ) )) ” 
  &&  “ (( &( "OS_TaskReturn" ) ) = ( &( "OS_TaskReturn" ) )) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ”
.

Definition OSInit_partial_solve_wit_27_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH7 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH8 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH9 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH10 : (queue_first_round_profile (os_init_sg (p)) )) (PreH11 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH14 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH15 : (queue_first_round_profile (os_init_sg (p)) )) (PreH16 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH17 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH18 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH19 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH20 : (mem_init_profile (os_init_sg (p)) )) (PreH21 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH22 : (mem_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH24 : (mem_init_profile (os_init_sg (p)) )) (PreH25 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH26 : (mem_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH28 : (flag_init_profile (os_init_sg (p)) )) (PreH29 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH32 : (flag_init_profile (os_init_sg (p)) )) (PreH33 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH34 : (flag_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH36 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH37 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH38 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH39 : (sizeof( "os_event" ) = 20)) (PreH40 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH41 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH42 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH43 : (event_table_layout_prop (os_init_sg (p)) )) (PreH44 : (init_event_list_profile (os_init_sg (p)) )) (PreH45 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH46 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH47 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH48 : (sizeof( "os_event" ) = 20)) (PreH49 : ((sizeof( "os_event" ) * 10) = 200)) (PreH50 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH51 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH52 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH53 : (event_table_layout_prop (os_init_sg (p)) )) (PreH54 : (init_event_list_profile (os_init_sg (p)) )) (PreH55 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH56 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH57 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH58 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH59 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH60 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH61 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH62 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH63 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH64 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH65 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH66 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH67 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH68 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH69 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH70 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH71 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_idle_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) )
  **  (os_init_idle_call_frame p )
|--
  “ (( &( "OS_TaskIdle" ) ) = ( &( "OS_TaskIdle" ) )) ” 
  &&  “ (( &( "OSTaskIdleStk" ) ) = ( &( "OSTaskIdleStk" ) )) ” 
  &&  “ (( &( "OS_TaskReturn" ) ) = ( &( "OS_TaskReturn" ) )) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_idle_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) )
  **  (os_init_idle_call_frame p )
.

Definition OSInit_partial_solve_wit_27 := OSInit_partial_solve_wit_27_pure -> OSInit_partial_solve_wit_27_aux.

Definition OSInit_partial_solve_wit_28 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH7 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH8 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH9 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH10 : (queue_first_round_profile (os_init_sg (p)) )) (PreH11 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH14 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH15 : (queue_first_round_profile (os_init_sg (p)) )) (PreH16 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH17 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH18 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH19 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH20 : (mem_init_profile (os_init_sg (p)) )) (PreH21 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH22 : (mem_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH24 : (mem_init_profile (os_init_sg (p)) )) (PreH25 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH26 : (mem_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH28 : (flag_init_profile (os_init_sg (p)) )) (PreH29 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH32 : (flag_init_profile (os_init_sg (p)) )) (PreH33 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH34 : (flag_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH36 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH37 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH38 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH39 : (sizeof( "os_event" ) = 20)) (PreH40 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH41 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH42 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH43 : (event_table_layout_prop (os_init_sg (p)) )) (PreH44 : (init_event_list_profile (os_init_sg (p)) )) (PreH45 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH46 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH47 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH48 : (sizeof( "os_event" ) = 20)) (PreH49 : ((sizeof( "os_event" ) * 10) = 200)) (PreH50 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH51 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH52 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH53 : (event_table_layout_prop (os_init_sg (p)) )) (PreH54 : (init_event_list_profile (os_init_sg (p)) )) (PreH55 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH56 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH57 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH58 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH59 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH60 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH61 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH62 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH63 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH64 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH65 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH66 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH67 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH68 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH69 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH70 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH71 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_task_idle_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )
  **  (os_init_idle_call_frame p )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_task_idle_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )
  **  (os_init_idle_call_frame p )
.

Definition OSInit_partial_solve_wit_29 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH7 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH8 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH9 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH10 : (queue_first_round_profile (os_init_sg (p)) )) (PreH11 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH14 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH15 : (queue_first_round_profile (os_init_sg (p)) )) (PreH16 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH17 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH18 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH19 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH20 : (mem_init_profile (os_init_sg (p)) )) (PreH21 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH22 : (mem_init_layout (os_init_sg (p)) )) (PreH23 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH24 : (mem_init_profile (os_init_sg (p)) )) (PreH25 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH26 : (mem_init_layout (os_init_sg (p)) )) (PreH27 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH28 : (flag_init_profile (os_init_sg (p)) )) (PreH29 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH30 : (flag_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH32 : (flag_init_profile (os_init_sg (p)) )) (PreH33 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH34 : (flag_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH36 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH37 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH38 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH39 : (sizeof( "os_event" ) = 20)) (PreH40 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH41 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH42 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH43 : (event_table_layout_prop (os_init_sg (p)) )) (PreH44 : (init_event_list_profile (os_init_sg (p)) )) (PreH45 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH46 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH47 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH48 : (sizeof( "os_event" ) = 20)) (PreH49 : ((sizeof( "os_event" ) * 10) = 200)) (PreH50 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH51 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH52 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH53 : (event_table_layout_prop (os_init_sg (p)) )) (PreH54 : (init_event_list_profile (os_init_sg (p)) )) (PreH55 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH56 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH57 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH58 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH59 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH60 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH61 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH62 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH63 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH64 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH65 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH66 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH67 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH68 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH69 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH70 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH71 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_before_stat p idle X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_before_stat p idle X )
.

Definition OSInit_partial_solve_wit_30_pure := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_stat_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) )
  **  (os_init_stat_call_frame p idle X )
|--
  “ (( &( "OS_TaskStat" ) ) = ( &( "OS_TaskStat" ) )) ” 
  &&  “ (( &( "OSTaskStatStk" ) ) = ( &( "OSTaskStatStk" ) )) ” 
  &&  “ (( &( "OS_TaskReturn" ) ) = ( &( "OS_TaskReturn" ) )) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ”
.

Definition OSInit_partial_solve_wit_30_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_stat_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) )
  **  (os_init_stat_call_frame p idle X )
|--
  “ (( &( "OS_TaskStat" ) ) = ( &( "OS_TaskStat" ) )) ” 
  &&  “ (( &( "OSTaskStatStk" ) ) = ( &( "OSTaskStatStk" ) )) ” 
  &&  “ (( &( "OS_TaskReturn" ) ) = ( &( "OS_TaskReturn" ) )) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_stat_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) )
  **  (os_init_stat_call_frame p idle X )
.

Definition OSInit_partial_solve_wit_30 := OSInit_partial_solve_wit_30_pure -> OSInit_partial_solve_wit_30_aux.

Definition OSInit_partial_solve_wit_31 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (init_task_stat_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )
  **  (os_init_stat_call_frame p idle X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (init_task_stat_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )
  **  (os_init_stat_call_frame p idle X )
.

Definition OSInit_partial_solve_wit_32 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_before_timer p idle stat X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_before_timer p idle stat X )
.

Definition OSInit_partial_solve_wit_33_pure := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  “ ((os_init_literals (p)) = (tmr_init_literals ((os_init_timer (p))))) ”
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  “ ((os_init_literals (p)) = (tmr_init_literals ((os_init_timer (p))))) ”
).

Definition OSInit_partial_solve_wit_33_pure_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  “ ((os_init_literals (p)) = (tmr_init_literals ((os_init_timer (p))))) ”
.

Definition OSInit_partial_solve_wit_33_aux := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  “ ((os_init_literals (p)) = (tmr_init_literals ((os_init_timer (p))))) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
.

Definition OSInit_partial_solve_wit_33 := OSInit_partial_solve_wit_33_pure -> OSInit_partial_solve_wit_33_aux.

Definition OSInit_partial_solve_wit_34 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (tmr_init_post (os_init_timer (p)) (os_init_named_call (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (tmr_init_post (os_init_timer (p)) (os_init_named_call (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
.

Definition OSInit_partial_solve_wit_35 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_after_timer_stage p idle stat timer X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_after_timer_stage p idle stat timer X )
.

Definition OSInit_partial_solve_wit_36 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_after_timer_stage p idle stat timer X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_after_timer_stage p idle stat timer X )
.

Definition OSInit_partial_solve_wit_37 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_after_end_stage p idle stat timer X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_after_end_stage p idle stat timer X )
.

Definition OSInit_partial_solve_wit_38 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) (PreH1 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH5 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH6 : (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) )) (PreH7 : (init_task_stat_stopped (os_init_named_state (idle)) )) (PreH8 : (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )) (PreH9 : (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) )) (PreH10 : (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH11 : (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (kernel_sched_ready_clients (os_init_critical (p)) )) (PreH13 : (kernel_tcb_stack_field_layout (os_init_sg (p)) )) (PreH14 : (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) )) (PreH15 : (init_task_idle_stopped (os_init_registered_state (p)) )) (PreH16 : (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )) (PreH17 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH18 : (queue_first_round_profile (os_init_sg (p)) )) (PreH19 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH20 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH21 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH22 : (valid_stable_glob_vars (os_init_sg (p)) )) (PreH23 : (queue_first_round_profile (os_init_sg (p)) )) (PreH24 : (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH25 : (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) )) (PreH26 : (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) )) (PreH27 : (q_init_table_endpoint_in_range (os_init_sg (p)) )) (PreH28 : (mem_init_profile (os_init_sg (p)) )) (PreH29 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH30 : (mem_init_layout (os_init_sg (p)) )) (PreH31 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH32 : (mem_init_profile (os_init_sg (p)) )) (PreH33 : (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH34 : (mem_init_layout (os_init_sg (p)) )) (PreH35 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH36 : (flag_init_profile (os_init_sg (p)) )) (PreH37 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH38 : (flag_init_layout (os_init_sg (p)) )) (PreH39 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH40 : (flag_init_profile (os_init_sg (p)) )) (PreH41 : (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH42 : (flag_init_layout (os_init_sg (p)) )) (PreH43 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH44 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH45 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH46 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH47 : (sizeof( "os_event" ) = 20)) (PreH48 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH49 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH50 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH51 : (event_table_layout_prop (os_init_sg (p)) )) (PreH52 : (init_event_list_profile (os_init_sg (p)) )) (PreH53 : ((osMaxEvents ((os_init_sg (p)))) = 10)) (PreH54 : ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) ))) (PreH55 : ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) ))) (PreH56 : (sizeof( "os_event" ) = 20)) (PreH57 : ((sizeof( "os_event" ) * 10) = 200)) (PreH58 : (0 <= (g_OSEventTbl ((os_init_sg (p)))))) (PreH59 : (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX)) (PreH60 : (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0)) (PreH61 : (event_table_layout_prop (os_init_sg (p)) )) (PreH62 : (init_event_list_profile (os_init_sg (p)) )) (PreH63 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH64 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH65 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH66 : (init_tcb_list_profile (os_init_sg (p)) )) (PreH67 : (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH68 : (init_tcb_list_layout (os_init_sg (p)) )) (PreH69 : (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p)))))) (PreH70 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p)))))) (PreH71 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p)))))) (PreH72 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p)))))) (PreH73 : (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p)))))) (PreH74 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p)))))) (PreH75 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p)))))) (PreH76 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p)))))) (PreH77 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p)))))) (PreH78 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p)))))) (PreH79 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p)))))) ,
  (os_init_after_end_stage p idle stat timer X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  (os_init_after_end_stage p idle stat timer X )
.

Definition OSInit_which_implies_wit_1 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_pre p X )
|--
  (os_init_hook_port_pre ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_exception_initial (p)) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_pre p X )
|--
  (os_init_hook_port_pre ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_exception_initial (p)) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
).

Definition OSInit_which_implies_wit_1_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_pre p X )
|--
  (os_init_hook_port_pre ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_exception_initial (p)) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_which_implies_wit_2 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_hook_port_post ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S (O)) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_hook_port_post ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S (O)) X )
).

Definition OSInit_which_implies_wit_2_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_hook_port_post ( &( "OS_CPU_ExceptStk" ) ) ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) (os_init_raw_call_frame (p) (O) (X)) )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S (O)) X )
.

Definition OSInit_which_implies_wit_3 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S (O)) X )
|--
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  ((( &( "OSTime" ) )) # UInt  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |->_)
  **  ((( &( "OSLockNesting" ) )) # UChar  |->_)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |->_)
  **  ((( &( "OSRunning" ) )) # UChar  |->_)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |->_)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |->_)
  **  ((( &( "OSStatRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |->_)
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S (O)) X )
|--
  EX (x_11: Z)  (x_10: Z)  (x_9: Z)  (x_8: Z)  (x_7: Z)  (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (( &( "OSTime" ) ) = (g_OSTime ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSLockNesting" ) ) = (g_OSLockNesting ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSRunning" ) ) = (g_OSRunning ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSStatRdy" ) ) = (g_OSStatRdy ((os_init_sg (p))))) ” 
  &&  “ (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID ((os_init_sg (p))))) ”
  &&  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> x_11)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> x_10)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> x_9)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> x_8)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> x_7)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> x_6)
  **  ((( &( "OSRunning" ) )) # UChar  |-> x_5)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> x_4)
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> x_3)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> x_2)
  **  ((( &( "OSTime" ) )) # UInt  |-> x)
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
).

Definition OSInit_which_implies_wit_4 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_misc_zero (os_init_sg (p)) )
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S ((S (O)))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_misc_zero (os_init_sg (p)) )
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S ((S (O)))) X )
).

Definition OSInit_which_implies_wit_4_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_misc_zero (os_init_sg (p)) )
  **  (os_init_raw_call_frame p (S (O)) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S ((S (O)))) X )
.

Definition OSInit_which_implies_wit_5 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S (O)))) X )
|--
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S (O)))) X )
|--
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
).

Definition OSInit_which_implies_wit_5_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S (O)))) X )
|--
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
.

Definition OSInit_which_implies_wit_6 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
).

Definition OSInit_which_implies_wit_6_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
  **  (os_init_raw_call_frame p (S ((S (O)))) X )
  **  (GlobalStrings (os_init_literals (p)) )
|--
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
.

Definition OSInit_which_implies_wit_7 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_profile (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout (os_init_sg (p)) ) ”
  &&  (init_tcb_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_layout (os_init_sg (p)) ) ” 
  &&  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_profile (os_init_sg (p)) ) ”
  &&  (init_tcb_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
).

Definition OSInit_which_implies_wit_7_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_layout (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_7_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_global_addresses (os_init_sg (p)) ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ”
.

Definition OSInit_which_implies_wit_7_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  “ (init_tcb_list_profile (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_7_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S (O)))))) X )
|--
  (init_tcb_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
.

Definition OSInit_which_implies_wit_8 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_tcb_list_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_tcb_list_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
).

Definition OSInit_which_implies_wit_8_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_tcb_list_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S (O)))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
.

Definition OSInit_which_implies_wit_9 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 20) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 200) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (init_event_list_profile (os_init_sg (p)) ) ”
  &&  (init_event_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (init_event_list_profile (os_init_sg (p)) ) ” 
  &&  “ (event_table_layout_prop (os_init_sg (p)) ) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ” 
  &&  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ” 
  &&  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ” 
  &&  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ”
  &&  (init_event_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
).

Definition OSInit_which_implies_wit_9_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (init_event_list_profile (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_9_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (event_table_layout_prop (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_9_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (((g_OSEventTbl ((os_init_sg (p)))) % ( 4 ) ) = 0) ”
.

Definition OSInit_which_implies_wit_9_split_goal_4 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (((g_OSEventTbl ((os_init_sg (p)))) + 200 ) <= UINT_MAX) ”
.

Definition OSInit_which_implies_wit_9_split_goal_5 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ (0 <= (g_OSEventTbl ((os_init_sg (p))))) ”
.

Definition OSInit_which_implies_wit_9_split_goal_6 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((g_OSEventFreeList ((os_init_sg (p)))) = ( &( "OSEventFreeList" ) )) ”
.

Definition OSInit_which_implies_wit_9_split_goal_7 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((g_OSEventTbl ((os_init_sg (p)))) = ( &( "OSEventTbl" ) )) ”
.

Definition OSInit_which_implies_wit_9_split_goal_8 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  “ ((osMaxEvents ((os_init_sg (p)))) = 10) ”
.

Definition OSInit_which_implies_wit_9_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S (O)))))))) X )
|--
  (init_event_list_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
.

Definition OSInit_which_implies_wit_10 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_event_list_post (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_event_list_post (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
).

Definition OSInit_which_implies_wit_10_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_event_list_post (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S (O)))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
.

Definition OSInit_which_implies_wit_11 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_profile (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_layout (os_init_sg (p)) ) ” 
  &&  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_profile (os_init_sg (p)) ) ”
  &&  (flag_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
).

Definition OSInit_which_implies_wit_11_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_layout (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_11_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_global_addresses (os_init_sg (p)) ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ”
.

Definition OSInit_which_implies_wit_11_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  “ (flag_init_profile (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_11_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  (flag_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
.

Definition OSInit_which_implies_wit_12 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (flag_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (flag_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
).

Definition OSInit_which_implies_wit_12_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (flag_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S (O)))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
.

Definition OSInit_which_implies_wit_13 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_profile (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_layout (os_init_sg (p)) ) ” 
  &&  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_profile (os_init_sg (p)) ) ”
  &&  (mem_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
).

Definition OSInit_which_implies_wit_13_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_layout (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_13_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_global_addresses (os_init_sg (p)) ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ”
.

Definition OSInit_which_implies_wit_13_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  “ (mem_init_profile (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_13_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  (mem_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
.

Definition OSInit_which_implies_wit_14 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (mem_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (mem_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
).

Definition OSInit_which_implies_wit_14_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (mem_init_post (os_init_sg (p)) (os_init_literals (p) (("?"%string))) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S (O)))))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
.

Definition OSInit_which_implies_wit_15 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ”
  &&  (queue_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ” 
  &&  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ” 
  &&  “ (queue_first_round_profile (os_init_sg (p)) ) ” 
  &&  “ (valid_stable_glob_vars (os_init_sg (p)) ) ”
  &&  (queue_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
).

Definition OSInit_which_implies_wit_15_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (q_init_table_endpoint_in_range (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_15_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (queue_table_layout_prop (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ”
.

Definition OSInit_which_implies_wit_15_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (os_q_free_list_addr (os_init_sg (p)) ( &( "OSQFreeList" ) ) ) ”
.

Definition OSInit_which_implies_wit_15_split_goal_4 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (os_q_table_addr (os_init_sg (p)) ( &( "OSQTbl" ) ) ) ”
.

Definition OSInit_which_implies_wit_15_split_goal_5 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (queue_first_round_profile (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_15_split_goal_6 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  “ (valid_stable_glob_vars (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_15_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  (queue_init_pre (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
.

Definition OSInit_which_implies_wit_16 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (OS_QInit_spec (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (OS_QInit_spec (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
).

Definition OSInit_which_implies_wit_16_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (OS_QInit_spec (os_init_sg (p)) )
  **  (GlobalStrings (os_init_literals (p)) )
  **  (os_init_raw_call_frame p (S ((S ((S ((S ((S ((S ((S (O)))))))))))))) X )
|--
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
.

Definition OSInit_which_implies_wit_17 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
|--
  (os_init_before_idle p X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
|--
  (os_init_before_idle p X )
).

Definition OSInit_which_implies_wit_17_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_raw_stage p (S ((S ((S ((S ((S ((S ((S ((S (O)))))))))))))))) X )
|--
  (os_init_before_idle p X )
.

Definition OSInit_which_implies_wit_18 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ”
  &&  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_idle_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) )
  **  (os_init_idle_call_frame p )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ” 
  &&  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ”
  &&  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_idle_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) )
  **  (os_init_idle_call_frame p )
).

Definition OSInit_which_implies_wit_18_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (init_task_idle_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (init_task_idle_stopped (os_init_registered_state (p)) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (task_create_runtime_call_input (init_task_idle_create_args (( &( "OS_TaskIdle" ) )) (( &( "OSTaskIdleStk" ) ))) (os_init_call (p)) (os_init_registered_state (p)) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_4 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_5 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_6 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_7 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_8 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ”
.

Definition OSInit_which_implies_wit_18_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (os_init_before_idle p X )
|--
  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_idle_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) )
  **  (os_init_idle_call_frame p )
.

Definition OSInit_which_implies_wit_19 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_task_idle_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )
  **  (os_init_idle_call_frame p )
|--
  EX (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) ,
  (init_task_idle_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskIdle" ) ) ( &( "OSTaskIdleStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_idle_lower (p)) (os_init_idle_frame (p)) (os_init_idle_upper (p)) (os_init_call (p)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_registered_state (p)) (os_init_idle_continuation (p) (X)) )
  **  (os_init_idle_call_frame p )
|--
  EX (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
).

Definition OSInit_which_implies_wit_20 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ”
  &&  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_stat_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) )
  **  (os_init_stat_call_frame p idle X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ” 
  &&  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ” 
  &&  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ” 
  &&  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ” 
  &&  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ” 
  &&  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ”
  &&  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_stat_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) )
  **  (os_init_stat_call_frame p idle X )
).

Definition OSInit_which_implies_wit_20_split_goal_1 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (init_task_stat_continuation_safe (os_init_environment (p)) (os_init_critical (p)) (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_2 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (init_task_stat_stopped (os_init_named_state (idle)) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_3 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (task_create_runtime_call_input (init_task_stat_create_args (( &( "OS_TaskStat" ) )) (( &( "OSTaskStatStk" ) ))) (os_init_named_call (idle)) (os_init_named_state (idle)) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_4 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (kernel_tcb_stack_field_layout (os_init_sg (p)) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_5 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (kernel_sched_ready_clients (os_init_critical (p)) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_6 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (os_sched_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_7 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (task_tcb_init_global_addresses (os_init_sg (p)) ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_8 := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  “ (task_create_stack_global_addresses (os_init_sg (p)) ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ”
.

Definition OSInit_which_implies_wit_20_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (os_init_before_stat p idle X )
|--
  (coq_prop (task_name_set_addresses ((os_init_sg (p))) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout ((os_init_sg (p)))) )
  **  (init_task_stat_entry (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) )
  **  (os_init_stat_call_frame p idle X )
.

Definition OSInit_which_implies_wit_21 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (init_task_stat_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )
  **  (os_init_stat_call_frame p idle X )
|--
  EX (stat: OsInitTaskResult) ,
  (os_init_before_timer p idle stat X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) ,
  (init_task_stat_continuation_post (os_init_environment (p)) (os_init_critical (p)) tmr_init_empty_local (os_init_sg (p)) ( &( "OS_TaskStat" ) ) ( &( "OSTaskStatStk" ) ) ( &( "OS_TaskReturn" ) ) (os_init_stat_lower (p)) (os_init_stat_frame (p)) (os_init_stat_upper (p)) (os_init_named_call (idle)) (os_init_mask (p)) (os_init_literals (p)) os_init_literal_keys (os_init_named_state (idle)) (os_init_stat_continuation (p) (X)) )
  **  (os_init_stat_call_frame p idle X )
|--
  EX (stat: OsInitTaskResult) ,
  (os_init_before_timer p idle stat X )
).

Definition OSInit_which_implies_wit_22 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) ,
  (os_init_before_timer p idle stat X )
|--
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) ,
  (os_init_before_timer p idle stat X )
|--
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
).

Definition OSInit_which_implies_wit_22_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) ,
  (os_init_before_timer p idle stat X )
|--
  (tmr_init_pre (os_init_timer (p)) (os_init_named_call (stat)) (os_init_named_state (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
.

Definition OSInit_which_implies_wit_23 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) ,
  (tmr_init_post (os_init_timer (p)) (os_init_named_call (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  EX (timer: OsInitTimerResult) ,
  (os_init_after_timer_stage p idle stat timer X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) ,
  (tmr_init_post (os_init_timer (p)) (os_init_named_call (stat)) (os_init_timer_continuation (X)) )
  **  (os_init_timer_call_frame p idle stat X )
|--
  EX (timer: OsInitTimerResult) ,
  (os_init_after_timer_stage p idle stat timer X )
).

Definition OSInit_which_implies_wit_24 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) ,
  (os_init_after_timer_stage p idle stat timer X )
|--
  (os_init_after_end_stage p idle stat timer X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) ,
  (os_init_after_timer_stage p idle stat timer X )
|--
  (os_init_after_end_stage p idle stat timer X )
).

Definition OSInit_which_implies_wit_24_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) ,
  (os_init_after_timer_stage p idle stat timer X )
|--
  (os_init_after_end_stage p idle stat timer X )
.

Definition OSInit_which_implies_wit_25 := 
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) ,
  (os_init_after_end_stage p idle stat timer X )
|--
  (os_init_return_stage p idle stat timer X )
) \/
(
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) ,
  (os_init_after_end_stage p idle stat timer X )
|--
  (os_init_return_stage p idle stat timer X )
).

Definition OSInit_which_implies_wit_25_split_goal_spatial := 
forall (X: (unit -> (OsInitState -> Prop))) (p: OsInitContext) (idle: OsInitTaskResult) (stat: OsInitTaskResult) (timer: OsInitTimerResult) ,
  (os_init_after_end_stage p idle stat timer X )
|--
  (os_init_return_stage p idle stat timer X )
.

Module Type VC_Correct.


Axiom proof_of_OSInit_return_wit_1 : OSInit_return_wit_1.
Axiom proof_of_OSInit_partial_solve_wit_1 : OSInit_partial_solve_wit_1.
Axiom proof_of_OSInit_partial_solve_wit_2_pure : OSInit_partial_solve_wit_2_pure.
Axiom proof_of_OSInit_partial_solve_wit_2 : OSInit_partial_solve_wit_2.
Axiom proof_of_OSInit_partial_solve_wit_3 : OSInit_partial_solve_wit_3.
Axiom proof_of_OSInit_partial_solve_wit_4 : OSInit_partial_solve_wit_4.
Axiom proof_of_OSInit_partial_solve_wit_5_pure : OSInit_partial_solve_wit_5_pure.
Axiom proof_of_OSInit_partial_solve_wit_5 : OSInit_partial_solve_wit_5.
Axiom proof_of_OSInit_partial_solve_wit_6 : OSInit_partial_solve_wit_6.
Axiom proof_of_OSInit_partial_solve_wit_7 : OSInit_partial_solve_wit_7.
Axiom proof_of_OSInit_partial_solve_wit_8 : OSInit_partial_solve_wit_8.
Axiom proof_of_OSInit_partial_solve_wit_9 : OSInit_partial_solve_wit_9.
Axiom proof_of_OSInit_partial_solve_wit_10 : OSInit_partial_solve_wit_10.
Axiom proof_of_OSInit_partial_solve_wit_11_pure : OSInit_partial_solve_wit_11_pure.
Axiom proof_of_OSInit_partial_solve_wit_11 : OSInit_partial_solve_wit_11.
Axiom proof_of_OSInit_partial_solve_wit_12 : OSInit_partial_solve_wit_12.
Axiom proof_of_OSInit_partial_solve_wit_13 : OSInit_partial_solve_wit_13.
Axiom proof_of_OSInit_partial_solve_wit_14_pure : OSInit_partial_solve_wit_14_pure.
Axiom proof_of_OSInit_partial_solve_wit_14 : OSInit_partial_solve_wit_14.
Axiom proof_of_OSInit_partial_solve_wit_15 : OSInit_partial_solve_wit_15.
Axiom proof_of_OSInit_partial_solve_wit_16 : OSInit_partial_solve_wit_16.
Axiom proof_of_OSInit_partial_solve_wit_17_pure : OSInit_partial_solve_wit_17_pure.
Axiom proof_of_OSInit_partial_solve_wit_17 : OSInit_partial_solve_wit_17.
Axiom proof_of_OSInit_partial_solve_wit_18 : OSInit_partial_solve_wit_18.
Axiom proof_of_OSInit_partial_solve_wit_19 : OSInit_partial_solve_wit_19.
Axiom proof_of_OSInit_partial_solve_wit_20_pure : OSInit_partial_solve_wit_20_pure.
Axiom proof_of_OSInit_partial_solve_wit_20 : OSInit_partial_solve_wit_20.
Axiom proof_of_OSInit_partial_solve_wit_21 : OSInit_partial_solve_wit_21.
Axiom proof_of_OSInit_partial_solve_wit_22 : OSInit_partial_solve_wit_22.
Axiom proof_of_OSInit_partial_solve_wit_23_pure : OSInit_partial_solve_wit_23_pure.
Axiom proof_of_OSInit_partial_solve_wit_23 : OSInit_partial_solve_wit_23.
Axiom proof_of_OSInit_partial_solve_wit_24 : OSInit_partial_solve_wit_24.
Axiom proof_of_OSInit_partial_solve_wit_25 : OSInit_partial_solve_wit_25.
Axiom proof_of_OSInit_partial_solve_wit_26 : OSInit_partial_solve_wit_26.
Axiom proof_of_OSInit_partial_solve_wit_27_pure : OSInit_partial_solve_wit_27_pure.
Axiom proof_of_OSInit_partial_solve_wit_27 : OSInit_partial_solve_wit_27.
Axiom proof_of_OSInit_partial_solve_wit_28 : OSInit_partial_solve_wit_28.
Axiom proof_of_OSInit_partial_solve_wit_29 : OSInit_partial_solve_wit_29.
Axiom proof_of_OSInit_partial_solve_wit_30_pure : OSInit_partial_solve_wit_30_pure.
Axiom proof_of_OSInit_partial_solve_wit_30 : OSInit_partial_solve_wit_30.
Axiom proof_of_OSInit_partial_solve_wit_31 : OSInit_partial_solve_wit_31.
Axiom proof_of_OSInit_partial_solve_wit_32 : OSInit_partial_solve_wit_32.
Axiom proof_of_OSInit_partial_solve_wit_33_pure : OSInit_partial_solve_wit_33_pure.
Axiom proof_of_OSInit_partial_solve_wit_33 : OSInit_partial_solve_wit_33.
Axiom proof_of_OSInit_partial_solve_wit_34 : OSInit_partial_solve_wit_34.
Axiom proof_of_OSInit_partial_solve_wit_35 : OSInit_partial_solve_wit_35.
Axiom proof_of_OSInit_partial_solve_wit_36 : OSInit_partial_solve_wit_36.
Axiom proof_of_OSInit_partial_solve_wit_37 : OSInit_partial_solve_wit_37.
Axiom proof_of_OSInit_partial_solve_wit_38 : OSInit_partial_solve_wit_38.
Axiom proof_of_OSInit_which_implies_wit_1 : OSInit_which_implies_wit_1.
Axiom proof_of_OSInit_which_implies_wit_2 : OSInit_which_implies_wit_2.
Axiom proof_of_OSInit_which_implies_wit_3 : OSInit_which_implies_wit_3.
Axiom proof_of_OSInit_which_implies_wit_4 : OSInit_which_implies_wit_4.
Axiom proof_of_OSInit_which_implies_wit_5 : OSInit_which_implies_wit_5.
Axiom proof_of_OSInit_which_implies_wit_6 : OSInit_which_implies_wit_6.
Axiom proof_of_OSInit_which_implies_wit_7 : OSInit_which_implies_wit_7.
Axiom proof_of_OSInit_which_implies_wit_8 : OSInit_which_implies_wit_8.
Axiom proof_of_OSInit_which_implies_wit_9 : OSInit_which_implies_wit_9.
Axiom proof_of_OSInit_which_implies_wit_10 : OSInit_which_implies_wit_10.
Axiom proof_of_OSInit_which_implies_wit_11 : OSInit_which_implies_wit_11.
Axiom proof_of_OSInit_which_implies_wit_12 : OSInit_which_implies_wit_12.
Axiom proof_of_OSInit_which_implies_wit_13 : OSInit_which_implies_wit_13.
Axiom proof_of_OSInit_which_implies_wit_14 : OSInit_which_implies_wit_14.
Axiom proof_of_OSInit_which_implies_wit_15 : OSInit_which_implies_wit_15.
Axiom proof_of_OSInit_which_implies_wit_16 : OSInit_which_implies_wit_16.
Axiom proof_of_OSInit_which_implies_wit_17 : OSInit_which_implies_wit_17.
Axiom proof_of_OSInit_which_implies_wit_18 : OSInit_which_implies_wit_18.
Axiom proof_of_OSInit_which_implies_wit_19 : OSInit_which_implies_wit_19.
Axiom proof_of_OSInit_which_implies_wit_20 : OSInit_which_implies_wit_20.
Axiom proof_of_OSInit_which_implies_wit_21 : OSInit_which_implies_wit_21.
Axiom proof_of_OSInit_which_implies_wit_22 : OSInit_which_implies_wit_22.
Axiom proof_of_OSInit_which_implies_wit_23 : OSInit_which_implies_wit_23.
Axiom proof_of_OSInit_which_implies_wit_24 : OSInit_which_implies_wit_24.
Axiom proof_of_OSInit_which_implies_wit_25 : OSInit_which_implies_wit_25.

End VC_Correct.
