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
Require Import Ucos2Verify.VC.code.time.spec.time_dly_resume_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.sched Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTimeDlyResume -----*)

Definition OSTimeDlyResume_safety_wit_1 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (63 <= priority)) (PreH9 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  “ False ”
.

Definition OSTimeDlyResume_safety_wit_2 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_save_output environment critical saved_local sg caller mask retval initial )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_safety_wit_3 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (selected_kernel_profile sg )) (PreH5 : (task_resume_tcb_pool_aligned sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_safety_wit_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_safety_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : (task_resume_tcb_pool_aligned sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTimeDlyResume_safety_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> 1)
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_safety_wit_7 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_safety_wit_8 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((dly (node)) <> 0)) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (selected_kernel_profile sg )) (PreH5 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH10 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH11 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (task_resume_y (node)))) (PreH13 : ((task_resume_y (node)) < 8)) (PreH14 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (55 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 55) ”
.

Definition OSTimeDlyResume_safety_wit_9 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) <> 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (55 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 55) ”
.

Definition OSTimeDlyResume_safety_wit_10 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved (time_dly_resume_state (sg) (acquired) (tid) (node)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_safety_wit_11 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved (time_dly_resume_state (sg) (acquired) (tid) (node)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDlyResume_entail_wit_1 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_save_output environment critical saved_local sg caller mask retval initial )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ (task_resume_tcb_pool_aligned sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired retval ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active retval acquired acquired )
  **  ((( &( "prio" ) )) # UChar  |-> priority)
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_save_output environment critical saved_local sg caller mask retval initial )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  “ (prio_pre = priority) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ (task_resume_tcb_pool_aligned sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired retval ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active retval acquired acquired )
).

Definition OSTimeDlyResume_entail_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 0)) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : (task_resume_tcb_pool_aligned sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
|--
  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> 0)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 0)) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : (task_resume_tcb_pool_aligned sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
).

Definition OSTimeDlyResume_entail_wit_2_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 0)) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : (task_resume_tcb_pool_aligned sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ”
.

Definition OSTimeDlyResume_entail_wit_2_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 0)) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : (task_resume_tcb_pool_aligned sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_entail_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
).

Definition OSTimeDlyResume_entail_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 1)) (PreH2 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (task_resume_tcb_pool_aligned sg )) (PreH8 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH11 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
|--
  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> 1)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 1)) (PreH2 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (task_resume_tcb_pool_aligned sg )) (PreH8 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH11 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
).

Definition OSTimeDlyResume_entail_wit_4_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 1)) (PreH2 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (task_resume_tcb_pool_aligned sg )) (PreH8 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH11 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ”
.

Definition OSTimeDlyResume_entail_wit_4_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = 1)) (PreH2 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (task_resume_tcb_pool_aligned sg )) (PreH8 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH11 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_entail_wit_5 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
).

Definition OSTimeDlyResume_entail_wit_6 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 1)) (PreH2 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (task_resume_tcb_pool_aligned sg )) (PreH8 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH11 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  EX (node: TaskAbstractState)  (tid: Z) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid))) ” 
  &&  “ ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node))) ” 
  &&  “ ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (task_resume_y (node))) ” 
  &&  “ ((task_resume_y (node)) < 8) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (node)))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 1)) (PreH2 : ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) <> 0)) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (task_resume_tcb_pool_aligned sg )) (PreH8 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH11 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  EX (node: TaskAbstractState)  (tid: Z) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid))) ” 
  &&  “ ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node))) ” 
  &&  “ ((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (task_resume_y (node))) ” 
  &&  “ ((task_resume_y (node)) < 8) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (node)))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&(((prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
).

Definition OSTimeDlyResume_entail_wit_7 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((dly (node)) = 0)) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (selected_kernel_profile sg )) (PreH5 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH10 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH11 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (task_resume_y (node)))) (PreH13 : ((task_resume_y (node)) < 8)) (PreH14 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((dly (node)) <= UINT_MAX)) (PreH2 : ((dly (node)) >= 0)) (PreH3 : ((dly (node)) = 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH12 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
).

Definition OSTimeDlyResume_entail_wit_7_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((dly (node)) <= UINT_MAX)) (PreH2 : ((dly (node)) >= 0)) (PreH3 : ((dly (node)) = 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH12 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired ) ”
.

Definition OSTimeDlyResume_entail_wit_7_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((dly (node)) <= UINT_MAX)) (PreH2 : ((dly (node)) >= 0)) (PreH3 : ((dly (node)) = 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH12 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_entail_wit_8 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 80 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved acquired )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 80 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
).

Definition OSTimeDlyResume_entail_wit_9_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) <> 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (node)))) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid))) ” 
  &&  “ ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node))) ” 
  &&  “ ((dly (node)) <> 0) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (task_resume_y (node))) ” 
  &&  “ ((task_resume_y (node)) < 8) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) <> 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  TT && emp 
|--
  “ ((Z.land (encode_task_status ((stat (node)))) (unsigned_last_nbits ((Z.lnot 55)) (8))) = (encode_task_status ((stat ((task_expire_delay (node))))))) ” 
  &&  “ (1 = (encode_pend_status ((statPend ((task_expire_delay (node))))))) ”
  &&  emp
).

Definition OSTimeDlyResume_entail_wit_9_1_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) <> 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((Z.land (encode_task_status ((stat (node)))) (unsigned_last_nbits ((Z.lnot 55)) (8))) = (encode_task_status ((stat ((task_expire_delay (node)))))))
.

Definition OSTimeDlyResume_entail_wit_9_1_split_goal_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) <> 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (1 = (encode_pend_status ((statPend ((task_expire_delay (node)))))))
.

Definition OSTimeDlyResume_entail_wit_9_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) = 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (node)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid))) ” 
  &&  “ ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node))) ” 
  &&  “ ((dly (node)) <> 0) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (task_resume_y (node))) ” 
  &&  “ ((task_resume_y (node)) < 8) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) = 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  TT && emp 
|--
  “ ((encode_task_status ((stat (node)))) = (encode_task_status ((stat ((task_expire_delay (node))))))) ” 
  &&  “ (0 = (encode_pend_status ((statPend ((task_expire_delay (node))))))) ”
  &&  emp
).

Definition OSTimeDlyResume_entail_wit_9_2_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) = 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((encode_task_status ((stat (node)))) = (encode_task_status ((stat ((task_expire_delay (node)))))))
.

Definition OSTimeDlyResume_entail_wit_9_2_split_goal_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (ptcb: Z) (tid: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (encode_task_status ((stat (node)))) 55) = 0)) (PreH2 : ((dly (node)) <> 0)) (PreH3 : (0 <= priority)) (PreH4 : (priority < 63)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (task_resume_y (node)))) (PreH14 : ((task_resume_y (node)) < 8)) (PreH15 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (0 = (encode_pend_status ((statPend ((task_expire_delay (node)))))))
.

Definition OSTimeDlyResume_entail_wit_10 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) = 0)) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (selected_kernel_profile sg )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH9 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH10 : ((dly (node)) <> 0)) (PreH11 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (task_resume_y (node)))) (PreH13 : ((task_resume_y (node)) < 8)) (PreH14 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_group (sg) (acquired))) (8)) (unsigned_last_nbits ((task_resume_bit_y (node))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_row (acquired) (node))) (8)) (unsigned_last_nbits ((task_resume_bit_x (node))) (8))))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) = 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : ((dly (node)) <> 0)) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_group (sg) (acquired))) (8)) (unsigned_last_nbits ((task_resume_bit_y (node))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_row (acquired) (node))) (8)) (unsigned_last_nbits ((task_resume_bit_x (node))) (8))))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
).

Definition OSTimeDlyResume_entail_wit_10_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) = 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : ((dly (node)) <> 0)) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_group (sg) (acquired))) (8)) (unsigned_last_nbits ((task_resume_bit_y (node))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_row (acquired) (node))) (8)) (unsigned_last_nbits ((task_resume_bit_x (node))) (8))))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ”
.

Definition OSTimeDlyResume_entail_wit_10_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) = 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : ((dly (node)) <> 0)) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_group (sg) (acquired))) (8)) (unsigned_last_nbits ((task_resume_bit_y (node))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_resume_row (acquired) (node))) (8)) (unsigned_last_nbits ((task_resume_bit_x (node))) (8))))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
.

Definition OSTimeDlyResume_entail_wit_11 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved (time_dly_resume_state (sg) (acquired) (tid) (node)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved (time_dly_resume_state (sg) (acquired) (tid) (node)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
).

Definition OSTimeDlyResume_entail_wit_12 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_resume_sched_safe environment critical sg returned mask restored 0 X ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  “ (task_resume_sched_safe environment critical sg returned mask restored 0 X ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
).

Definition OSTimeDlyResume_entail_wit_12_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  “ (task_resume_sched_safe environment critical sg returned mask restored 0 X ) ”
.

Definition OSTimeDlyResume_entail_wit_12_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
.

Definition OSTimeDlyResume_entail_wit_13 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) <> 0)) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (selected_kernel_profile sg )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH9 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH10 : ((dly (node)) <> 0)) (PreH11 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (task_resume_y (node)))) (PreH13 : ((task_resume_y (node)) < 8)) (PreH14 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) <> 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : ((dly (node)) <> 0)) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
).

Definition OSTimeDlyResume_entail_wit_13_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) <> 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : ((dly (node)) <> 0)) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ”
.

Definition OSTimeDlyResume_entail_wit_13_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (ptcb: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Z.land (encode_task_status ((stat ((task_expire_delay (node)))))) 8) <> 0)) (PreH4 : (0 <= priority)) (PreH5 : (priority < 63)) (PreH6 : (selected_kernel_profile sg )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : ((prioTbl ((TskState (acquired))) (priority)) = (PTTask (tid)))) (PreH11 : ((inUsedTaskStates ((TskState (acquired))) (tid)) = (Some (node)))) (PreH12 : ((dly (node)) <> 0)) (PreH13 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (task_resume_y (node)))) (PreH15 : ((task_resume_y (node)) < 8)) (PreH16 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend ((task_expire_delay (node)))))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (task_resume_y (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (task_resume_bit_x (node)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (task_resume_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_resume_group (sg) (acquired)))
  **  (((( &( "OSRdyTbl" ) ) + ((task_resume_y (node)) * sizeof(UCHAR)))) # UChar  |-> (task_resume_row (acquired) (node)))
  **  (time_dly_resume_node_frame sg acquired tid node )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
.

Definition OSTimeDlyResume_entail_wit_14 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved (time_dly_resume_state (sg) (acquired) (tid) (node)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_restore_output environment critical saved_local sg active saved (time_dly_resume_state (sg) (acquired) (tid) (node)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 false restored ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg returned mask restored )
).

Definition OSTimeDlyResume_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_resume_sched_safe environment critical sg returned mask restored 0 X )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_resume_sched_safe environment critical sg returned mask restored 0 X )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 0 X )
).

Definition OSTimeDlyResume_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_resume_sched_safe environment critical sg returned mask restored 0 X )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 0 X )
.

Definition OSTimeDlyResume_return_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 0 X )
).

Definition OSTimeDlyResume_return_wit_2_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 0 X )
.

Definition OSTimeDlyResume_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 80 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 80 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 80 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 80 X )
).

Definition OSTimeDlyResume_return_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 80 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 80 X )
.

Definition OSTimeDlyResume_return_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 67 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 67 X )
).

Definition OSTimeDlyResume_return_wit_4_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 67 X )
.

Definition OSTimeDlyResume_return_wit_5 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 67 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 67 X )
).

Definition OSTimeDlyResume_return_wit_5_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 67 false restored )) (PreH5 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg returned mask restored )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 67 X )
.

Definition OSTimeDlyResume_return_wit_6 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 42 X )
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 42 X )
).

Definition OSTimeDlyResume_return_wit_6_split_goal_spatial := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 42 X )
.

Definition OSTimeDlyResume_return_wit_7 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (63 <= priority)) (PreH9 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 42 X )
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (63 <= priority)) (PreH9 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 42 X )
).

Definition OSTimeDlyResume_return_wit_7_split_goal_spatial := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (63 <= priority)) (PreH9 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  (time_dly_resume_post environment critical saved_local sg caller mask initial priority 42 X )
.

Definition OSTimeDlyResume_partial_solve_wit_1 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre = priority)) (PreH3 : (0 <= priority)) (PreH4 : (priority <= 255)) (PreH5 : (selected_kernel_profile sg )) (PreH6 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (task_resume_tcb_pool_aligned sg )) (PreH9 : (UCOS2_state_inv sg initial )) (PreH10 : (task_resume_clients environment critical caller )) (PreH11 : (task_resume_caller_source sg caller initial )) (PreH12 : (time_dly_resume_entry_protocol critical sg caller initial )) (PreH13 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_closed environment critical saved_local sg caller mask initial )
|--
  “ (prio_pre < 63) ” 
  &&  “ (prio_pre = priority) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority <= 255) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_resume_tcb_pool_aligned sg ) ” 
  &&  “ (UCOS2_state_inv sg initial ) ” 
  &&  “ (task_resume_clients environment critical caller ) ” 
  &&  “ (task_resume_caller_source sg caller initial ) ” 
  &&  “ (time_dly_resume_entry_protocol critical sg caller initial ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_closed environment critical saved_local sg caller mask initial )
.

Definition OSTimeDlyResume_partial_solve_wit_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (selected_kernel_profile sg )) (PreH4 : (task_resume_tcb_pool_aligned sg )) (PreH5 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH8 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ (task_resume_tcb_pool_aligned sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_partial_solve_wit_3_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (selected_kernel_profile sg )) (PreH4 : (task_resume_tcb_pool_aligned sg )) (PreH5 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH8 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (UCOS2_inv sg acquired )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeDlyResume_partial_solve_wit_3_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (selected_kernel_profile sg )) (PreH4 : (task_resume_tcb_pool_aligned sg )) (PreH5 : ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) ))) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH8 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (UCOS2_inv sg acquired )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
|--
  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (selected_kernel_profile sg ) ” 
  &&  “ (task_resume_tcb_pool_aligned sg ) ” 
  &&  “ ((g_OSTCBTbl (sg)) = ( &( "OSTCBTbl" ) )) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_partial_solve_wit_3 := OSTimeDlyResume_partial_solve_wit_3_pure -> OSTimeDlyResume_partial_solve_wit_3_aux.

Definition OSTimeDlyResume_partial_solve_wit_4_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (saved = saved) ”
.

Definition OSTimeDlyResume_partial_solve_wit_4_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  “ (saved = saved) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_partial_solve_wit_4 := OSTimeDlyResume_partial_solve_wit_4_pure -> OSTimeDlyResume_partial_solve_wit_4_aux.

Definition OSTimeDlyResume_partial_solve_wit_5_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> 1)
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (saved = saved) ”
.

Definition OSTimeDlyResume_partial_solve_wit_5_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  “ (saved = saved) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (67) (false)) acquired ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_partial_solve_wit_5 := OSTimeDlyResume_partial_solve_wit_5_pure -> OSTimeDlyResume_partial_solve_wit_5_aux.

Definition OSTimeDlyResume_partial_solve_wit_6_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (saved = saved) ”
.

Definition OSTimeDlyResume_partial_solve_wit_6_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  “ (saved = saved) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (80) (false)) acquired ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_partial_solve_wit_6 := OSTimeDlyResume_partial_solve_wit_6_pure -> OSTimeDlyResume_partial_solve_wit_6_aux.

Definition OSTimeDlyResume_partial_solve_wit_7_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (saved = saved) ”
.

Definition OSTimeDlyResume_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
|--
  “ (saved = saved) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (true)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
.

Definition OSTimeDlyResume_partial_solve_wit_7 := OSTimeDlyResume_partial_solve_wit_7_pure -> OSTimeDlyResume_partial_solve_wit_7_aux.

Definition OSTimeDlyResume_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (tid: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_resume_sched_safe environment critical sg returned mask restored 0 X )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeDlyResume_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (task_resume_sched_safe environment critical sg returned mask restored 0 X )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_return_facts environment critical sg caller returned mask initial priority 0 true restored ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (task_resume_sched_safe environment critical sg returned mask restored 0 X ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
.

Definition OSTimeDlyResume_partial_solve_wit_8 := OSTimeDlyResume_partial_solve_wit_8_pure -> OSTimeDlyResume_partial_solve_wit_8_aux.

Definition OSTimeDlyResume_partial_solve_wit_9_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> saved)
|--
  “ (saved = saved) ”
.

Definition OSTimeDlyResume_partial_solve_wit_9_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (priority: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (PreH1 : (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved )) (PreH2 : (0 <= priority)) (PreH3 : (priority < 63)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) )) (PreH6 : (time_dly_resume_safe environment critical sg caller mask priority initial X )) ,
  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
|--
  “ (saved = saved) ” 
  &&  “ (time_dly_resume_acquire_facts environment critical sg caller active mask initial acquired saved ) ” 
  &&  “ (0 <= priority) ” 
  &&  “ (priority < 63) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_resume_critical_code sg priority acquired (pair (0) (false)) (time_dly_resume_state (sg) (acquired) (tid) (node)) ) ” 
  &&  “ (time_dly_resume_safe environment critical sg caller mask priority initial X ) ”
  &&  (task_resume_masked environment critical saved_local sg active saved acquired (time_dly_resume_state (sg) (acquired) (tid) (node)) )
.

Definition OSTimeDlyResume_partial_solve_wit_9 := OSTimeDlyResume_partial_solve_wit_9_pure -> OSTimeDlyResume_partial_solve_wit_9_aux.

Definition OSTimeDlyResume_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  (UCOS2_inv sg acquired )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  (UCOS2_inv sg acquired )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
).

Definition OSTimeDlyResume_which_implies_wit_1_split_goal_spatial := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (saved: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) ,
  (task_resume_masked environment critical saved_local sg active saved acquired acquired )
|--
  (UCOS2_inv sg acquired )
  **  (task_resume_mask_frame environment critical saved_local sg active saved acquired acquired )
.

Definition OSTimeDlyResume_which_implies_wit_2 := 
(
forall (priority: Z) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
) \/
(
forall (priority: Z) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
).

Definition OSTimeDlyResume_which_implies_wit_2_split_goal_1 := 
forall (priority: Z) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
.

Definition OSTimeDlyResume_which_implies_wit_2_split_goal_spatial := 
forall (priority: Z) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= priority)) (PreH2 : (priority < 63)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg acquired )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (priority * sizeof(PTR)))) # Ptr  |-> (prio_tbl_entry_to_addr (sg) ((prioTbl ((TskState (acquired))) (priority)))))
  **  (task_resume_priority_frame sg acquired priority )
.

Module Type VC_Correct.


Axiom proof_of_OSTimeDlyResume_safety_wit_1 : OSTimeDlyResume_safety_wit_1.
Axiom proof_of_OSTimeDlyResume_safety_wit_2 : OSTimeDlyResume_safety_wit_2.
Axiom proof_of_OSTimeDlyResume_safety_wit_3 : OSTimeDlyResume_safety_wit_3.
Axiom proof_of_OSTimeDlyResume_safety_wit_4 : OSTimeDlyResume_safety_wit_4.
Axiom proof_of_OSTimeDlyResume_safety_wit_5 : OSTimeDlyResume_safety_wit_5.
Axiom proof_of_OSTimeDlyResume_safety_wit_6 : OSTimeDlyResume_safety_wit_6.
Axiom proof_of_OSTimeDlyResume_safety_wit_7 : OSTimeDlyResume_safety_wit_7.
Axiom proof_of_OSTimeDlyResume_safety_wit_8 : OSTimeDlyResume_safety_wit_8.
Axiom proof_of_OSTimeDlyResume_safety_wit_9 : OSTimeDlyResume_safety_wit_9.
Axiom proof_of_OSTimeDlyResume_safety_wit_10 : OSTimeDlyResume_safety_wit_10.
Axiom proof_of_OSTimeDlyResume_safety_wit_11 : OSTimeDlyResume_safety_wit_11.
Axiom proof_of_OSTimeDlyResume_entail_wit_1 : OSTimeDlyResume_entail_wit_1.
Axiom proof_of_OSTimeDlyResume_entail_wit_2 : OSTimeDlyResume_entail_wit_2.
Axiom proof_of_OSTimeDlyResume_entail_wit_3 : OSTimeDlyResume_entail_wit_3.
Axiom proof_of_OSTimeDlyResume_entail_wit_4 : OSTimeDlyResume_entail_wit_4.
Axiom proof_of_OSTimeDlyResume_entail_wit_5 : OSTimeDlyResume_entail_wit_5.
Axiom proof_of_OSTimeDlyResume_entail_wit_6 : OSTimeDlyResume_entail_wit_6.
Axiom proof_of_OSTimeDlyResume_entail_wit_7 : OSTimeDlyResume_entail_wit_7.
Axiom proof_of_OSTimeDlyResume_entail_wit_8 : OSTimeDlyResume_entail_wit_8.
Axiom proof_of_OSTimeDlyResume_entail_wit_9_1 : OSTimeDlyResume_entail_wit_9_1.
Axiom proof_of_OSTimeDlyResume_entail_wit_9_2 : OSTimeDlyResume_entail_wit_9_2.
Axiom proof_of_OSTimeDlyResume_entail_wit_10 : OSTimeDlyResume_entail_wit_10.
Axiom proof_of_OSTimeDlyResume_entail_wit_11 : OSTimeDlyResume_entail_wit_11.
Axiom proof_of_OSTimeDlyResume_entail_wit_12 : OSTimeDlyResume_entail_wit_12.
Axiom proof_of_OSTimeDlyResume_entail_wit_13 : OSTimeDlyResume_entail_wit_13.
Axiom proof_of_OSTimeDlyResume_entail_wit_14 : OSTimeDlyResume_entail_wit_14.
Axiom proof_of_OSTimeDlyResume_return_wit_1 : OSTimeDlyResume_return_wit_1.
Axiom proof_of_OSTimeDlyResume_return_wit_2 : OSTimeDlyResume_return_wit_2.
Axiom proof_of_OSTimeDlyResume_return_wit_3 : OSTimeDlyResume_return_wit_3.
Axiom proof_of_OSTimeDlyResume_return_wit_4 : OSTimeDlyResume_return_wit_4.
Axiom proof_of_OSTimeDlyResume_return_wit_5 : OSTimeDlyResume_return_wit_5.
Axiom proof_of_OSTimeDlyResume_return_wit_6 : OSTimeDlyResume_return_wit_6.
Axiom proof_of_OSTimeDlyResume_return_wit_7 : OSTimeDlyResume_return_wit_7.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_1 : OSTimeDlyResume_partial_solve_wit_1.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_2 : OSTimeDlyResume_partial_solve_wit_2.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_3_pure : OSTimeDlyResume_partial_solve_wit_3_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_3 : OSTimeDlyResume_partial_solve_wit_3.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_4_pure : OSTimeDlyResume_partial_solve_wit_4_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_4 : OSTimeDlyResume_partial_solve_wit_4.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_5_pure : OSTimeDlyResume_partial_solve_wit_5_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_5 : OSTimeDlyResume_partial_solve_wit_5.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_6_pure : OSTimeDlyResume_partial_solve_wit_6_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_6 : OSTimeDlyResume_partial_solve_wit_6.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_7_pure : OSTimeDlyResume_partial_solve_wit_7_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_7 : OSTimeDlyResume_partial_solve_wit_7.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_8_pure : OSTimeDlyResume_partial_solve_wit_8_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_8 : OSTimeDlyResume_partial_solve_wit_8.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_9_pure : OSTimeDlyResume_partial_solve_wit_9_pure.
Axiom proof_of_OSTimeDlyResume_partial_solve_wit_9 : OSTimeDlyResume_partial_solve_wit_9.
Axiom proof_of_OSTimeDlyResume_which_implies_wit_1 : OSTimeDlyResume_which_implies_wit_1.
Axiom proof_of_OSTimeDlyResume_which_implies_wit_2 : OSTimeDlyResume_which_implies_wit_2.

End VC_Correct.
