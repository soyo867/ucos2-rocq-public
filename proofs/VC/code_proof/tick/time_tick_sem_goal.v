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
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_sem_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSSemPost -----*)

Definition OSSemPost_safety_wit_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (sem_post_profile sg )) (PreH3 : (time_tick_post_readable sg before pe )) (PreH4 : (event_table_layout_prop sg )) (PreH5 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_2 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (sem_post_lookup before eid node )) (PreH7 : ((time_tick_sem_type (node)) = 3)) (PreH8 : ((time_tick_sem_type (node)) = 3)) (PreH9 : (pe <> 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (sem_post_lookup before eid node )) (PreH15 : (0 <= (time_tick_sem_type (node)))) (PreH16 : ((time_tick_sem_type (node)) <= 255)) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (time_tick_post_readable sg before pe )) (PreH22 : (event_table_layout_prop sg )) (PreH23 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_3 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_lookup before eid node )) (PreH4 : ((time_tick_sem_type (node)) = 3)) (PreH5 : ((sem_post_group (before) (node)) <> 0)) (PreH6 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH7 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_lookup before eid node )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (pe <> 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (sem_post_lookup before eid node )) (PreH17 : ((time_tick_sem_type (node)) = 3)) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : (pe <> 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (event_object_layout_prop sg eid )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_lookup before eid node )) (PreH25 : (0 <= (time_tick_sem_type (node)))) (PreH26 : ((time_tick_sem_type (node)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (sem_post_profile sg )) (PreH31 : (time_tick_post_readable sg before pe )) (PreH32 : (event_table_layout_prop sg )) (PreH33 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_4 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (time_tick_sem_result sg pe before 0 after )) (PreH2 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_5 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) )) (PreH2 : ((encode_event_cnt_value (node)) < 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_6 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 51 before )) (PreH2 : ((encode_event_cnt_value (node)) >= 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_return_wit_1 := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 51 before )) (PreH2 : ((encode_event_cnt_value (node)) >= 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 51 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 51 before )) (PreH2 : ((encode_event_cnt_value (node)) >= 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 51 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
).

Definition OSSemPost_return_wit_2 := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) )) (PreH2 : ((encode_event_cnt_value (node)) < 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 0 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) )) (PreH2 : ((encode_event_cnt_value (node)) < 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 0 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
).

Definition OSSemPost_return_wit_3 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (after_2)) > 0)) (PreH2 : (time_tick_sem_result sg pe before 0 after_2 )) (PreH3 : ((os_sched_ints (after_2)) = (os_sched_ints (before)))) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) <> 0)) (PreH8 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH9 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (interrupt_saved_value 192 retval )) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (sem_post_lookup before eid node )) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : (pe <> 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (event_object_layout_prop sg eid )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_lookup before eid node )) (PreH27 : (0 <= (time_tick_sem_type (node)))) (PreH28 : ((time_tick_sem_type (node)) <= 255)) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (sem_post_profile sg )) (PreH33 : (time_tick_post_readable sg before pe )) (PreH34 : (event_table_layout_prop sg )) (PreH35 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after_2 )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 0 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
.

Definition OSSemPost_return_wit_4 := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : (time_tick_sem_result sg pe before 1 before )) (PreH2 : ((time_tick_sem_type (node)) <> 3)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (sem_post_lookup before eid node )) (PreH9 : (0 <= (time_tick_sem_type (node)))) (PreH10 : ((time_tick_sem_type (node)) <= 255)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (sem_post_profile sg )) (PreH15 : (time_tick_post_readable sg before pe )) (PreH16 : (event_table_layout_prop sg )) (PreH17 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 1 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : (time_tick_sem_result sg pe before 1 before )) (PreH2 : ((time_tick_sem_type (node)) <> 3)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (sem_post_lookup before eid node )) (PreH9 : (0 <= (time_tick_sem_type (node)))) (PreH10 : ((time_tick_sem_type (node)) <= 255)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (sem_post_profile sg )) (PreH15 : (time_tick_post_readable sg before pe )) (PreH16 : (event_table_layout_prop sg )) (PreH17 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 1 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
).

Definition OSSemPost_return_wit_5 := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (time_tick_post_readable sg before pe )) (PreH5 : (event_table_layout_prop sg )) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 4 after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (time_tick_post_readable sg before pe )) (PreH5 : (event_table_layout_prop sg )) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((os_sched_ints (before)) > 0)) ,
  TT && emp 
|--
  “ (time_tick_sem_result sg pevent_pre before 4 before ) ”
  &&  emp
).

Definition OSSemPost_return_wit_5_split_goal_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (time_tick_post_readable sg before pe )) (PreH5 : (event_table_layout_prop sg )) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sem_result sg pevent_pre before 4 before )
.

Definition OSSemPost_partial_solve_wit_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (time_tick_post_readable sg before pe )) (PreH5 : (event_table_layout_prop sg )) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
.

Definition OSSemPost_partial_solve_wit_2_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (sem_post_profile sg )) (PreH5 : (time_tick_post_readable sg before pe )) (PreH6 : (event_table_layout_prop sg )) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
|--
  “ (pe <> 0) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSSemPost_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (sem_post_profile sg )) (PreH5 : (time_tick_post_readable sg before pe )) (PreH6 : (event_table_layout_prop sg )) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
|--
  “ (pe <> 0) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_2 := OSSemPost_partial_solve_wit_2_pure -> OSSemPost_partial_solve_wit_2_aux.

Definition OSSemPost_partial_solve_wit_3_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : ((time_tick_sem_type (node)) <> 3)) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_lookup before eid node )) (PreH8 : (0 <= (time_tick_sem_type (node)))) (PreH9 : ((time_tick_sem_type (node)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (sem_post_profile sg )) (PreH14 : (time_tick_post_readable sg before pe )) (PreH15 : (event_table_layout_prop sg )) (PreH16 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) <> 3) ”
.

Definition OSSemPost_partial_solve_wit_3_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : ((time_tick_sem_type (node)) <> 3)) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_lookup before eid node )) (PreH8 : (0 <= (time_tick_sem_type (node)))) (PreH9 : ((time_tick_sem_type (node)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (sem_post_profile sg )) (PreH14 : (time_tick_post_readable sg before pe )) (PreH15 : (event_table_layout_prop sg )) (PreH16 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : ((os_sched_ints (before)) > 0)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) <> 3) ” 
  &&  “ ((time_tick_sem_type (node)) <> 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_3 := OSSemPost_partial_solve_wit_3_pure -> OSSemPost_partial_solve_wit_3_aux.

Definition OSSemPost_partial_solve_wit_4_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : ((time_tick_sem_type (node)) = 3)) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_lookup before eid node )) (PreH8 : (0 <= (time_tick_sem_type (node)))) (PreH9 : ((time_tick_sem_type (node)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (sem_post_profile sg )) (PreH14 : (time_tick_post_readable sg before pe )) (PreH15 : (event_table_layout_prop sg )) (PreH16 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ”
.

Definition OSSemPost_partial_solve_wit_4_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : ((time_tick_sem_type (node)) = 3)) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_lookup before eid node )) (PreH8 : (0 <= (time_tick_sem_type (node)))) (PreH9 : ((time_tick_sem_type (node)) <= 255)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (sem_post_profile sg )) (PreH14 : (time_tick_post_readable sg before pe )) (PreH15 : (event_table_layout_prop sg )) (PreH16 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : ((os_sched_ints (before)) > 0)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_4 := OSSemPost_partial_solve_wit_4_pure -> OSSemPost_partial_solve_wit_4_aux.

Definition OSSemPost_partial_solve_wit_5 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((time_tick_sem_type (node)) = 3)) (PreH8 : (pe <> 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (valid_event_id sg eid )) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (sem_post_lookup before eid node )) (PreH14 : (0 <= (time_tick_sem_type (node)))) (PreH15 : ((time_tick_sem_type (node)) <= 255)) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (sem_post_profile sg )) (PreH20 : (time_tick_post_readable sg before pe )) (PreH21 : (event_table_layout_prop sg )) (PreH22 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_6_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (sem_post_lookup before eid node )) (PreH7 : ((time_tick_sem_type (node)) = 3)) (PreH8 : ((time_tick_sem_type (node)) = 3)) (PreH9 : (pe <> 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (sem_post_lookup before eid node )) (PreH15 : (0 <= (time_tick_sem_type (node)))) (PreH16 : ((time_tick_sem_type (node)) <= 255)) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (time_tick_post_readable sg before pe )) (PreH22 : (event_table_layout_prop sg )) (PreH23 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ”
.

Definition OSSemPost_partial_solve_wit_6_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (pe <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (sem_post_lookup before eid node )) (PreH7 : ((time_tick_sem_type (node)) = 3)) (PreH8 : ((time_tick_sem_type (node)) = 3)) (PreH9 : (pe <> 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (sem_post_lookup before eid node )) (PreH15 : (0 <= (time_tick_sem_type (node)))) (PreH16 : ((time_tick_sem_type (node)) <= 255)) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (time_tick_post_readable sg before pe )) (PreH22 : (event_table_layout_prop sg )) (PreH23 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_6 := OSSemPost_partial_solve_wit_6_pure -> OSSemPost_partial_solve_wit_6_aux.

Definition OSSemPost_partial_solve_wit_7_pure := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (interrupt_saved_value 192 retval )) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : ((time_tick_sem_type (node)) = 3)) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : (0 <= (time_tick_sem_type (node)))) (PreH21 : ((time_tick_sem_type (node)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (time_tick_post_readable sg before pe )) (PreH27 : (event_table_layout_prop sg )) (PreH28 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ”
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (pe <> 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : ((time_tick_sem_type (node)) = 3)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_lookup before eid node )) (PreH21 : (0 <= (time_tick_sem_type (node)))) (PreH22 : ((time_tick_sem_type (node)) <= 255)) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (sem_post_profile sg )) (PreH27 : (time_tick_post_readable sg before pe )) (PreH28 : (event_table_layout_prop sg )) (PreH29 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((sem_post_group (before) (node)) <> 0) ”
).

Definition OSSemPost_partial_solve_wit_7_pure_split_goal_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (pe <> 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : ((time_tick_sem_type (node)) = 3)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_lookup before eid node )) (PreH21 : (0 <= (time_tick_sem_type (node)))) (PreH22 : ((time_tick_sem_type (node)) <= 255)) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (sem_post_profile sg )) (PreH27 : (time_tick_post_readable sg before pe )) (PreH28 : (event_table_layout_prop sg )) (PreH29 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((sem_post_group (before) (node)) <> 0) ”
.

Definition OSSemPost_partial_solve_wit_7_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (interrupt_saved_value 192 retval )) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : ((time_tick_sem_type (node)) = 3)) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : (0 <= (time_tick_sem_type (node)))) (PreH21 : ((time_tick_sem_type (node)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (time_tick_post_readable sg before pe )) (PreH27 : (event_table_layout_prop sg )) (PreH28 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : ((os_sched_ints (before)) > 0)) ,
  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (unmap_table_rep sg )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
.

Definition OSSemPost_partial_solve_wit_7 := OSSemPost_partial_solve_wit_7_pure -> OSSemPost_partial_solve_wit_7_aux.

Definition OSSemPost_partial_solve_wit_8_pure := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_lookup before eid node )) (PreH4 : ((time_tick_sem_type (node)) = 3)) (PreH5 : ((sem_post_group (before) (node)) <> 0)) (PreH6 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH7 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_lookup before eid node )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (pe <> 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (sem_post_lookup before eid node )) (PreH17 : ((time_tick_sem_type (node)) = 3)) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : (pe <> 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (event_object_layout_prop sg eid )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_lookup before eid node )) (PreH25 : (0 <= (time_tick_sem_type (node)))) (PreH26 : ((time_tick_sem_type (node)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (sem_post_profile sg )) (PreH31 : (time_tick_post_readable sg before pe )) (PreH32 : (event_table_layout_prop sg )) (PreH33 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSSemPost_partial_solve_wit_8_pure_split_goal_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSSemPost_partial_solve_wit_8_pure_split_goal_2 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSSemPost_partial_solve_wit_8_pure_split_goal_3 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSSemPost_partial_solve_wit_8_pure_split_goal_4 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSSemPost_partial_solve_wit_8_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_lookup before eid node )) (PreH4 : ((time_tick_sem_type (node)) = 3)) (PreH5 : ((sem_post_group (before) (node)) <> 0)) (PreH6 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH7 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_lookup before eid node )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (pe <> 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (sem_post_lookup before eid node )) (PreH17 : ((time_tick_sem_type (node)) = 3)) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : (pe <> 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (event_object_layout_prop sg eid )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_lookup before eid node )) (PreH25 : (0 <= (time_tick_sem_type (node)))) (PreH26 : ((time_tick_sem_type (node)) <= 255)) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (sem_post_profile sg )) (PreH31 : (time_tick_post_readable sg before pe )) (PreH32 : (event_table_layout_prop sg )) (PreH33 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : ((os_sched_ints (before)) > 0)) ,
  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
.

Definition OSSemPost_partial_solve_wit_8 := OSSemPost_partial_solve_wit_8_pure -> OSSemPost_partial_solve_wit_8_aux.

Definition OSSemPost_partial_solve_wit_9_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (retval_2: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (sem_post_lookup before eid node )) (PreH3 : ((time_tick_sem_type (node)) = 3)) (PreH4 : ((sem_post_group (before) (node)) <> 0)) (PreH5 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH6 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_lookup before eid node )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (pe <> 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (sem_post_lookup before eid node )) (PreH16 : ((time_tick_sem_type (node)) = 3)) (PreH17 : ((time_tick_sem_type (node)) = 3)) (PreH18 : (pe <> 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (event_object_layout_prop sg eid )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (sem_post_lookup before eid node )) (PreH24 : (0 <= (time_tick_sem_type (node)))) (PreH25 : ((time_tick_sem_type (node)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (sem_post_profile sg )) (PreH30 : (time_tick_post_readable sg before pe )) (PreH31 : (event_table_layout_prop sg )) (PreH32 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : ((os_sched_ints (before)) > 0)) ,
  (event_task_rdy_post sg (TskState (before)) eid node tid old 0 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ”
.

Definition OSSemPost_partial_solve_wit_9_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (retval_2: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (sem_post_lookup before eid node )) (PreH3 : ((time_tick_sem_type (node)) = 3)) (PreH4 : ((sem_post_group (before) (node)) <> 0)) (PreH5 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH6 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_lookup before eid node )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (pe <> 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (sem_post_lookup before eid node )) (PreH16 : ((time_tick_sem_type (node)) = 3)) (PreH17 : ((time_tick_sem_type (node)) = 3)) (PreH18 : (pe <> 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (event_object_layout_prop sg eid )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (sem_post_lookup before eid node )) (PreH24 : (0 <= (time_tick_sem_type (node)))) (PreH25 : ((time_tick_sem_type (node)) <= 255)) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (sem_post_profile sg )) (PreH30 : (time_tick_post_readable sg before pe )) (PreH31 : (event_table_layout_prop sg )) (PreH32 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : ((os_sched_ints (before)) > 0)) ,
  (event_task_rdy_post sg (TskState (before)) eid node tid old 0 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (event_task_rdy_post sg (TskState (before)) eid node tid old 0 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) retval_2 )
  **  (sem_post_wake_frame sg before eid tid )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
.

Definition OSSemPost_partial_solve_wit_9 := OSSemPost_partial_solve_wit_9_pure -> OSSemPost_partial_solve_wit_9_aux.

Definition OSSemPost_partial_solve_wit_10_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (time_tick_sem_result sg pe before 0 after )) (PreH2 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSSemPost_partial_solve_wit_10_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (time_tick_sem_result sg pe before 0 after )) (PreH2 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_sem_result sg pe before 0 after ) ” 
  &&  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
  **  (critical_region_inside critical sg invocation region_entry )
.

Definition OSSemPost_partial_solve_wit_10 := OSSemPost_partial_solve_wit_10_pure -> OSSemPost_partial_solve_wit_10_aux.

Definition OSSemPost_partial_solve_wit_11_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (time_tick_sem_result sg pe before 0 after )) (PreH2 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
  **  (critical_region_inside critical sg invocation region_entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
.

Definition OSSemPost_partial_solve_wit_11_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (time_tick_sem_result sg pe before 0 after )) (PreH2 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH8 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_lookup before eid node )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_lookup before eid node )) (PreH18 : ((time_tick_sem_type (node)) = 3)) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : (pe <> 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_lookup before eid node )) (PreH26 : (0 <= (time_tick_sem_type (node)))) (PreH27 : ((time_tick_sem_type (node)) <= 255)) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (sem_post_profile sg )) (PreH32 : (time_tick_post_readable sg before pe )) (PreH33 : (event_table_layout_prop sg )) (PreH34 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
  **  (critical_region_inside critical sg invocation region_entry )
|--
  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) > 0) ” 
  &&  “ (time_tick_sem_result sg pe before 0 after ) ” 
  &&  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_11 := OSSemPost_partial_solve_wit_11_pure -> OSSemPost_partial_solve_wit_11_aux.

Definition OSSemPost_partial_solve_wit_12_pure := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (after)) > 0)) (PreH2 : (time_tick_sem_result sg pe before 0 after )) (PreH3 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) <> 0)) (PreH8 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH9 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (interrupt_saved_value 192 retval )) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (sem_post_lookup before eid node )) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : (pe <> 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (event_object_layout_prop sg eid )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_lookup before eid node )) (PreH27 : (0 <= (time_tick_sem_type (node)))) (PreH28 : ((time_tick_sem_type (node)) <= 255)) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (sem_post_profile sg )) (PreH33 : (time_tick_post_readable sg before pe )) (PreH34 : (event_table_layout_prop sg )) (PreH35 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((os_sched_ints (after)) > 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ”
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((os_sched_ints (after)) > 0)) (PreH4 : (time_tick_sem_result sg pe before 0 after )) (PreH5 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_lookup before eid node )) (PreH8 : ((time_tick_sem_type (node)) = 3)) (PreH9 : ((sem_post_group (before) (node)) <> 0)) (PreH10 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH11 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (sem_post_lookup before eid node )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (interrupt_saved_value 192 retval )) (PreH16 : (pe <> 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_lookup before eid node )) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : ((time_tick_sem_type (node)) = 3)) (PreH23 : (pe <> 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (valid_event_id sg eid )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (sem_post_lookup before eid node )) (PreH29 : (0 <= (time_tick_sem_type (node)))) (PreH30 : ((time_tick_sem_type (node)) <= 255)) (PreH31 : (UCOS2_state_inv sg before )) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (sem_post_profile sg )) (PreH35 : (time_tick_post_readable sg before pe )) (PreH36 : (event_table_layout_prop sg )) (PreH37 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ”
).

Definition OSSemPost_partial_solve_wit_12_pure_split_goal_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((os_sched_ints (after)) > 0)) (PreH4 : (time_tick_sem_result sg pe before 0 after )) (PreH5 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_lookup before eid node )) (PreH8 : ((time_tick_sem_type (node)) = 3)) (PreH9 : ((sem_post_group (before) (node)) <> 0)) (PreH10 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH11 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (sem_post_lookup before eid node )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (interrupt_saved_value 192 retval )) (PreH16 : (pe <> 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_lookup before eid node )) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : ((time_tick_sem_type (node)) = 3)) (PreH23 : (pe <> 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (valid_event_id sg eid )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (sem_post_lookup before eid node )) (PreH29 : (0 <= (time_tick_sem_type (node)))) (PreH30 : ((time_tick_sem_type (node)) <= 255)) (PreH31 : (UCOS2_state_inv sg before )) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (sem_post_profile sg )) (PreH35 : (time_tick_post_readable sg before pe )) (PreH36 : (event_table_layout_prop sg )) (PreH37 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ”
.

Definition OSSemPost_partial_solve_wit_12_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (tid: Z) (old: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (after)) > 0)) (PreH2 : (time_tick_sem_result sg pe before 0 after )) (PreH3 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) <> 0)) (PreH8 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) (PreH9 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0)) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (interrupt_saved_value 192 retval )) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (sem_post_lookup before eid node )) (PreH19 : ((time_tick_sem_type (node)) = 3)) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : (pe <> 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (event_object_layout_prop sg eid )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_lookup before eid node )) (PreH27 : (0 <= (time_tick_sem_type (node)))) (PreH28 : ((time_tick_sem_type (node)) <= 255)) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (sem_post_profile sg )) (PreH33 : (time_tick_post_readable sg before pe )) (PreH34 : (event_table_layout_prop sg )) (PreH35 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : ((os_sched_ints (before)) > 0)) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
|--
  “ ((os_sched_ints (after)) > 0) ” 
  &&  “ (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg))) ” 
  &&  “ ((os_sched_ints (after)) > 0) ” 
  &&  “ (time_tick_sem_result sg pe before 0 after ) ” 
  &&  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
.

Definition OSSemPost_partial_solve_wit_12 := OSSemPost_partial_solve_wit_12_pure -> OSSemPost_partial_solve_wit_12_aux.

Definition OSSemPost_partial_solve_wit_13_pure := 
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (interrupt_saved_value 192 retval )) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : ((time_tick_sem_type (node)) = 3)) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : (0 <= (time_tick_sem_type (node)))) (PreH21 : ((time_tick_sem_type (node)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (time_tick_post_readable sg before pe )) (PreH27 : (event_table_layout_prop sg )) (PreH28 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ”
) \/
(
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (pe <> 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : ((time_tick_sem_type (node)) = 3)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_lookup before eid node )) (PreH21 : (0 <= (time_tick_sem_type (node)))) (PreH22 : ((time_tick_sem_type (node)) <= 255)) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (sem_post_profile sg )) (PreH27 : (time_tick_post_readable sg before pe )) (PreH28 : (event_table_layout_prop sg )) (PreH29 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((sem_post_group (before) (node)) = 0) ”
).

Definition OSSemPost_partial_solve_wit_13_pure_split_goal_1 := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (pe <> 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (event_object_layout_prop sg eid )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : ((time_tick_sem_type (node)) = 3)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_lookup before eid node )) (PreH21 : (0 <= (time_tick_sem_type (node)))) (PreH22 : ((time_tick_sem_type (node)) <= 255)) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (sem_post_profile sg )) (PreH27 : (time_tick_post_readable sg before pe )) (PreH28 : (event_table_layout_prop sg )) (PreH29 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((sem_post_group (before) (node)) = 0) ”
.

Definition OSSemPost_partial_solve_wit_13_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (interrupt_saved_value 192 retval )) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (sem_post_lookup before eid node )) (PreH12 : ((time_tick_sem_type (node)) = 3)) (PreH13 : ((time_tick_sem_type (node)) = 3)) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : (0 <= (time_tick_sem_type (node)))) (PreH21 : ((time_tick_sem_type (node)) <= 255)) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (time_tick_post_readable sg before pe )) (PreH27 : (event_table_layout_prop sg )) (PreH28 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : ((os_sched_ints (before)) > 0)) ,
  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_13 := OSSemPost_partial_solve_wit_13_pure -> OSSemPost_partial_solve_wit_13_aux.

Definition OSSemPost_partial_solve_wit_14_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_cnt_value (node)) < 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) < 65535) ”
.

Definition OSSemPost_partial_solve_wit_14_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_cnt_value (node)) < 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) < 65535) ” 
  &&  “ ((encode_event_cnt_value (node)) < 65535) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_14 := OSSemPost_partial_solve_wit_14_pure -> OSSemPost_partial_solve_wit_14_aux.

Definition OSSemPost_partial_solve_wit_15_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) )) (PreH2 : ((encode_event_cnt_value (node)) < 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSSemPost_partial_solve_wit_15_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) )) (PreH2 : ((encode_event_cnt_value (node)) < 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) ) ” 
  &&  “ ((encode_event_cnt_value (node)) < 65535) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_15 := OSSemPost_partial_solve_wit_15_pure -> OSSemPost_partial_solve_wit_15_aux.

Definition OSSemPost_partial_solve_wit_16_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_cnt_value (node)) >= 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ ((encode_event_cnt_value (node)) >= 65535) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ”
.

Definition OSSemPost_partial_solve_wit_16_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_cnt_value (node)) >= 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ ((encode_event_cnt_value (node)) >= 65535) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ” 
  &&  “ ((encode_event_cnt_value (node)) >= 65535) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_16 := OSSemPost_partial_solve_wit_16_pure -> OSSemPost_partial_solve_wit_16_aux.

Definition OSSemPost_partial_solve_wit_17_pure := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 51 before )) (PreH2 : ((encode_event_cnt_value (node)) >= 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSSemPost_partial_solve_wit_17_aux := 
forall (pevent_pre: Z) (pe: Z) (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (eid: Z) (node: OSEventAbstractState) (retval: Z) (PreH1 : (time_tick_sem_result sg pe before 51 before )) (PreH2 : ((encode_event_cnt_value (node)) >= 65535)) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0)) (PreH11 : (event_object_layout_prop sg eid )) (PreH12 : (sem_post_lookup before eid node )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (interrupt_saved_value 192 retval )) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_lookup before eid node )) (PreH20 : ((time_tick_sem_type (node)) = 3)) (PreH21 : ((time_tick_sem_type (node)) = 3)) (PreH22 : (pe <> 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_lookup before eid node )) (PreH28 : (0 <= (time_tick_sem_type (node)))) (PreH29 : ((time_tick_sem_type (node)) <= 255)) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (sem_post_profile sg )) (PreH34 : (time_tick_post_readable sg before pe )) (PreH35 : (event_table_layout_prop sg )) (PreH36 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : ((os_sched_ints (before)) > 0)) ,
  (UCOS2_inv sg before )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_sem_result sg pe before 51 before ) ” 
  &&  “ ((encode_event_cnt_value (node)) >= 65535) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (before) (node))) (32)) = 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (time_tick_post_readable sg before pe ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before)) > 0) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCOS2_inv sg before )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_partial_solve_wit_17 := OSSemPost_partial_solve_wit_17_pure -> OSSemPost_partial_solve_wit_17_aux.

Definition OSSemPost_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
).

Definition OSSemPost_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSSemPost_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg before )
  **  (unmap_table_rep sg )
.

Definition OSSemPost_which_implies_wit_2 := 
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pe <> 0)) (PreH2 : (time_tick_post_readable sg before pe )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (UCOS2_state_inv sg before )) ,
  (UCOS2_inv sg before )
|--
  EX (node: OSEventAbstractState)  (eid: Z) ,
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
) \/
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pe <> 0)) (PreH2 : (time_tick_post_readable sg before pe )) (PreH3 : (event_table_layout_prop sg )) (PreH4 : (UCOS2_state_inv sg before )) ,
  (UCOS2_inv sg before )
|--
  EX (node: OSEventAbstractState)  (eid: Z) ,
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (0 <= (time_tick_sem_type (node))) ” 
  &&  “ ((time_tick_sem_type (node)) <= 255) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
).

Definition OSSemPost_which_implies_wit_3 := 
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) <> 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 1 before ) ”
  &&  (UCOS2_inv sg before )
) \/
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) <> 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 1 before ) ”
  &&  (UCOS2_inv sg before )
).

Definition OSSemPost_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) <> 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 1 before ) ”
.

Definition OSSemPost_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) <> 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  (UCOS2_inv sg before )
.

Definition OSSemPost_which_implies_wit_4 := 
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ”
  &&  (UCOS2_inv sg before )
) \/
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  (UCOS2_inv sg before )
).

Definition OSSemPost_which_implies_wit_4_split_goal_spatial := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (time_tick_sem_type (node)))
  **  (sem_post_type_frame sg before eid node )
|--
  (UCOS2_inv sg before )
.

Definition OSSemPost_which_implies_wit_5 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (sem_post_lookup before eid node )) ,
  (UCOS2_inv sg before )
|--
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (sem_post_lookup before eid node )) ,
  (UCOS2_inv sg before )
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
).

Definition OSSemPost_which_implies_wit_5_split_goal_1 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (sem_post_lookup before eid node )) ,
  (UCOS2_inv sg before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSSemPost_which_implies_wit_5_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (sem_post_lookup before eid node )) ,
  (UCOS2_inv sg before )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
.

Definition OSSemPost_which_implies_wit_6 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (unmap_table_rep sg )
|--
  EX (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ”
  &&  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) <> 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
  **  (unmap_table_rep sg )
|--
  EX (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) <> 0) ” 
  &&  “ (event_task_rdy_entry sg (TskState (before)) eid node tid old ) ”
  &&  (event_task_rdy_pre sg (TskState (before)) eid node tid old 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) )
  **  (sem_post_wake_frame sg before eid tid )
).

Definition OSSemPost_which_implies_wit_7 := 
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (priority: Z) (old: TaskAbstractState) (tid: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (sem_post_lookup before eid node )) (PreH3 : ((time_tick_sem_type (node)) = 3)) (PreH4 : ((sem_post_group (before) (node)) <> 0)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) ,
  (event_task_rdy_post sg (TskState (before)) eid node tid old 0 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) priority )
  **  (sem_post_wake_frame sg before eid tid )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 0 after ) ” 
  &&  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ”
  &&  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
) \/
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (priority: Z) (old: TaskAbstractState) (tid: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (sem_post_lookup before eid node )) (PreH3 : ((time_tick_sem_type (node)) = 3)) (PreH4 : ((sem_post_group (before) (node)) <> 0)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (event_task_rdy_entry sg (TskState (before)) eid node tid old )) ,
  (event_task_rdy_post sg (TskState (before)) eid node tid old 0 1 0 (time_tick_sem_ready_group (before)) (time_tick_sem_ready_rows (before)) priority )
  **  (sem_post_wake_frame sg before eid tid )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg pe before 0 after ) ” 
  &&  “ ((os_sched_ints (after)) = (os_sched_ints (before))) ”
  &&  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
).

Definition OSSemPost_which_implies_wit_8 := 
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
|--
  “ ((os_sched_ints (after)) > 0) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
) \/
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
|--
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
).

Definition OSSemPost_which_implies_wit_8_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (after)) = (os_sched_ints (before)))) (PreH2 : ((os_sched_ints (before)) > 0)) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (UCOS2_inv sg after )
  **  (unmap_table_rep sg )
|--
  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
.

Definition OSSemPost_which_implies_wit_9 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) = 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
|--
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_lookup before eid node ) ” 
  &&  “ ((time_tick_sem_type (node)) = 3) ” 
  &&  “ ((sem_post_group (before) (node)) = 0) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ” 
  &&  “ ((encode_event_cnt_value (node)) <= 65535) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) = 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
|--
  “ ((encode_event_cnt_value (node)) <= 65535) ” 
  &&  “ (0 <= (encode_event_cnt_value (node))) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
).

Definition OSSemPost_which_implies_wit_9_split_goal_1 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) = 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
|--
  “ ((encode_event_cnt_value (node)) <= 65535) ”
.

Definition OSSemPost_which_implies_wit_9_split_goal_2 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) = 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
|--
  “ (0 <= (encode_event_cnt_value (node))) ”
.

Definition OSSemPost_which_implies_wit_9_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_lookup before eid node )) (PreH5 : ((time_tick_sem_type (node)) = 3)) (PreH6 : ((sem_post_group (before) (node)) = 0)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (before) (node)))
  **  (sem_post_group_frame sg before eid node )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
.

Definition OSSemPost_which_implies_wit_10 := 
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) < 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) ) ”
  &&  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
) \/
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) < 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) ) ”
  &&  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
).

Definition OSSemPost_which_implies_wit_10_split_goal_1 := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) < 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint (before) (eid) (node)) ) ”
.

Definition OSSemPost_which_implies_wit_10_split_goal_spatial := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : (0 <= (encode_event_cnt_value (node)))) (PreH9 : ((encode_event_cnt_value (node)) < 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (node)) + 1 ))
  **  (sem_post_count_frame sg before eid node )
|--
  (UCOS2_inv sg (sem_post_count_checkpoint (before) (eid) (node)) )
.

Definition OSSemPost_which_implies_wit_11 := 
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : ((encode_event_cnt_value (node)) >= 65535)) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 51 before ) ”
  &&  (UCOS2_inv sg before )
) \/
(
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : ((encode_event_cnt_value (node)) >= 65535)) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 51 before ) ”
  &&  (UCOS2_inv sg before )
).

Definition OSSemPost_which_implies_wit_11_split_goal_1 := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : ((encode_event_cnt_value (node)) >= 65535)) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
|--
  “ (time_tick_sem_result sg pe before 51 before ) ”
.

Definition OSSemPost_which_implies_wit_11_split_goal_spatial := 
forall (pe: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (eid: Z) (node: OSEventAbstractState) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_lookup before eid node )) (PreH6 : ((time_tick_sem_type (node)) = 3)) (PreH7 : ((sem_post_group (before) (node)) = 0)) (PreH8 : ((encode_event_cnt_value (node)) >= 65535)) (PreH9 : ((encode_event_cnt_value (node)) <= 65535)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (node)))
  **  (sem_post_count_frame sg before eid node )
|--
  (UCOS2_inv sg before )
.

Module Type VC_Correct.


Axiom proof_of_OSSemPost_safety_wit_1 : OSSemPost_safety_wit_1.
Axiom proof_of_OSSemPost_safety_wit_2 : OSSemPost_safety_wit_2.
Axiom proof_of_OSSemPost_safety_wit_3 : OSSemPost_safety_wit_3.
Axiom proof_of_OSSemPost_safety_wit_4 : OSSemPost_safety_wit_4.
Axiom proof_of_OSSemPost_safety_wit_5 : OSSemPost_safety_wit_5.
Axiom proof_of_OSSemPost_safety_wit_6 : OSSemPost_safety_wit_6.
Axiom proof_of_OSSemPost_return_wit_1 : OSSemPost_return_wit_1.
Axiom proof_of_OSSemPost_return_wit_2 : OSSemPost_return_wit_2.
Axiom proof_of_OSSemPost_return_wit_3 : OSSemPost_return_wit_3.
Axiom proof_of_OSSemPost_return_wit_4 : OSSemPost_return_wit_4.
Axiom proof_of_OSSemPost_return_wit_5 : OSSemPost_return_wit_5.
Axiom proof_of_OSSemPost_partial_solve_wit_1 : OSSemPost_partial_solve_wit_1.
Axiom proof_of_OSSemPost_partial_solve_wit_2_pure : OSSemPost_partial_solve_wit_2_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_2 : OSSemPost_partial_solve_wit_2.
Axiom proof_of_OSSemPost_partial_solve_wit_3_pure : OSSemPost_partial_solve_wit_3_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_3 : OSSemPost_partial_solve_wit_3.
Axiom proof_of_OSSemPost_partial_solve_wit_4_pure : OSSemPost_partial_solve_wit_4_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_4 : OSSemPost_partial_solve_wit_4.
Axiom proof_of_OSSemPost_partial_solve_wit_5 : OSSemPost_partial_solve_wit_5.
Axiom proof_of_OSSemPost_partial_solve_wit_6_pure : OSSemPost_partial_solve_wit_6_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_6 : OSSemPost_partial_solve_wit_6.
Axiom proof_of_OSSemPost_partial_solve_wit_7_pure : OSSemPost_partial_solve_wit_7_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_7 : OSSemPost_partial_solve_wit_7.
Axiom proof_of_OSSemPost_partial_solve_wit_8_pure : OSSemPost_partial_solve_wit_8_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_8 : OSSemPost_partial_solve_wit_8.
Axiom proof_of_OSSemPost_partial_solve_wit_9_pure : OSSemPost_partial_solve_wit_9_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_9 : OSSemPost_partial_solve_wit_9.
Axiom proof_of_OSSemPost_partial_solve_wit_10_pure : OSSemPost_partial_solve_wit_10_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_10 : OSSemPost_partial_solve_wit_10.
Axiom proof_of_OSSemPost_partial_solve_wit_11_pure : OSSemPost_partial_solve_wit_11_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_11 : OSSemPost_partial_solve_wit_11.
Axiom proof_of_OSSemPost_partial_solve_wit_12_pure : OSSemPost_partial_solve_wit_12_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_12 : OSSemPost_partial_solve_wit_12.
Axiom proof_of_OSSemPost_partial_solve_wit_13_pure : OSSemPost_partial_solve_wit_13_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_13 : OSSemPost_partial_solve_wit_13.
Axiom proof_of_OSSemPost_partial_solve_wit_14_pure : OSSemPost_partial_solve_wit_14_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_14 : OSSemPost_partial_solve_wit_14.
Axiom proof_of_OSSemPost_partial_solve_wit_15_pure : OSSemPost_partial_solve_wit_15_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_15 : OSSemPost_partial_solve_wit_15.
Axiom proof_of_OSSemPost_partial_solve_wit_16_pure : OSSemPost_partial_solve_wit_16_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_16 : OSSemPost_partial_solve_wit_16.
Axiom proof_of_OSSemPost_partial_solve_wit_17_pure : OSSemPost_partial_solve_wit_17_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_17 : OSSemPost_partial_solve_wit_17.
Axiom proof_of_OSSemPost_which_implies_wit_1 : OSSemPost_which_implies_wit_1.
Axiom proof_of_OSSemPost_which_implies_wit_2 : OSSemPost_which_implies_wit_2.
Axiom proof_of_OSSemPost_which_implies_wit_3 : OSSemPost_which_implies_wit_3.
Axiom proof_of_OSSemPost_which_implies_wit_4 : OSSemPost_which_implies_wit_4.
Axiom proof_of_OSSemPost_which_implies_wit_5 : OSSemPost_which_implies_wit_5.
Axiom proof_of_OSSemPost_which_implies_wit_6 : OSSemPost_which_implies_wit_6.
Axiom proof_of_OSSemPost_which_implies_wit_7 : OSSemPost_which_implies_wit_7.
Axiom proof_of_OSSemPost_which_implies_wit_8 : OSSemPost_which_implies_wit_8.
Axiom proof_of_OSSemPost_which_implies_wit_9 : OSSemPost_which_implies_wit_9.
Axiom proof_of_OSSemPost_which_implies_wit_10 : OSSemPost_which_implies_wit_10.
Axiom proof_of_OSSemPost_which_implies_wit_11 : OSSemPost_which_implies_wit_11.

End VC_Correct.
