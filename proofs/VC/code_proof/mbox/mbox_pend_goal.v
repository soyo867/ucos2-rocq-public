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
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_pend_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMboxPend -----*)

Definition OSMboxPend_safety_wit_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (timeout_pre = ticks)) (PreH3 : (perr_pre = pd)) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (sem_pend_profile sg )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (kernel_tcb_stack_field_layout sg )) (PreH8 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH9 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH10 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH11 : (pe = 0)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (timeout_pre = ticks)) (PreH3 : (perr_pre = pd)) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (sem_pend_profile sg )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (kernel_tcb_stack_field_layout sg )) (PreH8 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH9 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH10 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH11 : (pe <> 0)) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_3 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMboxPend_safety_wit_4 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe <> 0)) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMboxPend_safety_wit_5 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_6 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (mbox_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_7 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_8 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (mbox_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_9 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (mbox_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_output (MboxPendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_10 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mailbox: MboxFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH6 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH7 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH9 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (timeout_pre <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (timeout_pre >= 0)) (PreH19 : (0 >= 0)) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (timeout_pre = ticks)) (PreH29 : (perr_pre = pd)) (PreH30 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH31 : (sem_pend_profile sg )) (PreH32 : (mbox_accept_profile sg )) (PreH33 : (kernel_tcb_stack_field_layout sg )) (PreH34 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH35 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH36 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH37 : (pe <> 0)) (PreH38 : (event_object_layout_prop sg eid )) (PreH39 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_11 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mailbox: MboxFields) (PreH1 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_12 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint )) (PreH2 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_13 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH2 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output (Some ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask waiting )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_14 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (environment = (Some (owned_2)))) (PreH4 : (external = (task_stack_call_external (owned_2)))) (PreH5 : (platform = (task_stack_call_platform (owned_2)))) (PreH6 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH7 : (mbox_pend_sched_admitted environment critical )) (PreH8 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH9 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : ((mbox_message_ptr (mailbox)) = 0)) (PreH20 : (environment = (Some (owned)))) (PreH21 : (external = (task_stack_call_external (owned)))) (PreH22 : (platform = (task_stack_call_platform (owned)))) (PreH23 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH24 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH25 : ((mbox_message_ptr (mailbox)) = 0)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (mbox_pend_api_prefix pe before eid )) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH29 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH30 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH33 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH38 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH39 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH40 : (timeout_pre <= UINT_MAX)) (PreH41 : (0 <= UINT_MAX)) (PreH42 : (timeout_pre >= 0)) (PreH43 : (0 >= 0)) (PreH44 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH45 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH46 : (pe = (event_addr (sg) (eid)))) (PreH47 : (valid_event_id sg eid )) (PreH48 : (q_query_public_slot before eid observed )) (PreH49 : (UCOS2_state_inv sg before )) (PreH50 : (pevent_pre <> 0)) (PreH51 : (pevent_pre = pe)) (PreH52 : (timeout_pre = ticks)) (PreH53 : (perr_pre = pd)) (PreH54 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH55 : (sem_pend_profile sg )) (PreH56 : (mbox_accept_profile sg )) (PreH57 : (kernel_tcb_stack_field_layout sg )) (PreH58 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH59 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH60 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH61 : (pe <> 0)) (PreH62 : (event_object_layout_prop sg eid )) (PreH63 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH64 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_output (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg scheduled mask retval_2 selected )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_15 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH69 : (2 = (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_16 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : ((node.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH9 : (interrupt_saved_value mask retval_2 )) (PreH10 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH11 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (environment = (Some (owned_2)))) (PreH14 : (external = (task_stack_call_external (owned_2)))) (PreH15 : (platform = (task_stack_call_platform (owned_2)))) (PreH16 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH17 : (mbox_pend_sched_admitted environment critical )) (PreH18 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH19 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH20 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH21 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH22 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH23 : ((old.(dly) ) <= UINT_MAX)) (PreH24 : (retval <= UINT_MAX)) (PreH25 : (ticks <= UINT_MAX)) (PreH26 : ((old.(dly) ) >= 0)) (PreH27 : (retval >= 0)) (PreH28 : (ticks >= 0)) (PreH29 : ((mbox_message_ptr (mailbox)) = 0)) (PreH30 : (environment = (Some (owned)))) (PreH31 : (external = (task_stack_call_external (owned)))) (PreH32 : (platform = (task_stack_call_platform (owned)))) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH35 : ((mbox_message_ptr (mailbox)) = 0)) (PreH36 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (mbox_pend_api_prefix pe before eid )) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH39 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH40 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH42 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH43 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH44 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH48 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH49 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH50 : (timeout_pre <= UINT_MAX)) (PreH51 : (0 <= UINT_MAX)) (PreH52 : (timeout_pre >= 0)) (PreH53 : (0 >= 0)) (PreH54 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH55 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH56 : (pe = (event_addr (sg) (eid)))) (PreH57 : (valid_event_id sg eid )) (PreH58 : (q_query_public_slot before eid observed )) (PreH59 : (UCOS2_state_inv sg before )) (PreH60 : (pevent_pre <> 0)) (PreH61 : (pevent_pre = pe)) (PreH62 : (timeout_pre = ticks)) (PreH63 : (perr_pre = pd)) (PreH64 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH65 : (sem_pend_profile sg )) (PreH66 : (mbox_accept_profile sg )) (PreH67 : (kernel_tcb_stack_field_layout sg )) (PreH68 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH69 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH70 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH71 : (pe <> 0)) (PreH72 : (event_object_layout_prop sg eid )) (PreH73 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH74 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH75 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH76 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH77 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_17 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : ((node.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH9 : (interrupt_saved_value mask retval_2 )) (PreH10 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH11 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (environment = (Some (owned_2)))) (PreH14 : (external = (task_stack_call_external (owned_2)))) (PreH15 : (platform = (task_stack_call_platform (owned_2)))) (PreH16 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH17 : (mbox_pend_sched_admitted environment critical )) (PreH18 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH19 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH20 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH21 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH22 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH23 : ((old.(dly) ) <= UINT_MAX)) (PreH24 : (retval <= UINT_MAX)) (PreH25 : (ticks <= UINT_MAX)) (PreH26 : ((old.(dly) ) >= 0)) (PreH27 : (retval >= 0)) (PreH28 : (ticks >= 0)) (PreH29 : ((mbox_message_ptr (mailbox)) = 0)) (PreH30 : (environment = (Some (owned)))) (PreH31 : (external = (task_stack_call_external (owned)))) (PreH32 : (platform = (task_stack_call_platform (owned)))) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH35 : ((mbox_message_ptr (mailbox)) = 0)) (PreH36 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (mbox_pend_api_prefix pe before eid )) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH39 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH40 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH42 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH43 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH44 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH48 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH49 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH50 : (timeout_pre <= UINT_MAX)) (PreH51 : (0 <= UINT_MAX)) (PreH52 : (timeout_pre >= 0)) (PreH53 : (0 >= 0)) (PreH54 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH55 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH56 : (pe = (event_addr (sg) (eid)))) (PreH57 : (valid_event_id sg eid )) (PreH58 : (q_query_public_slot before eid observed )) (PreH59 : (UCOS2_state_inv sg before )) (PreH60 : (pevent_pre <> 0)) (PreH61 : (pevent_pre = pe)) (PreH62 : (timeout_pre = ticks)) (PreH63 : (perr_pre = pd)) (PreH64 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH65 : (sem_pend_profile sg )) (PreH66 : (mbox_accept_profile sg )) (PreH67 : (kernel_tcb_stack_field_layout sg )) (PreH68 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH69 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH70 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH71 : (pe <> 0)) (PreH72 : (event_object_layout_prop sg eid )) (PreH73 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH74 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH75 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH76 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH77 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_18 := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_19 := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_safety_wit_20 := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> code)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPend_entail_wit_1 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH2 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_query_public_slot before eid observed )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (timeout_pre = ticks)) (PreH10 : (perr_pre = pd)) (PreH11 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH12 : (sem_pend_profile sg )) (PreH13 : (mbox_accept_profile sg )) (PreH14 : (kernel_tcb_stack_field_layout sg )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH17 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH18 : (pe <> 0)) (PreH19 : (event_object_layout_prop sg eid )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (timeout_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (timeout_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_query_public_slot before eid observed )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (timeout_pre = ticks)) (PreH14 : (perr_pre = pd)) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (sem_pend_profile sg )) (PreH17 : (mbox_accept_profile sg )) (PreH18 : (kernel_tcb_stack_field_layout sg )) (PreH19 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH20 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH21 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH22 : (pe <> 0)) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ”
  &&  emp
).

Definition OSMboxPend_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (timeout_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (timeout_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_query_public_slot before eid observed )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (timeout_pre = ticks)) (PreH14 : (perr_pre = pd)) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (sem_pend_profile sg )) (PreH17 : (mbox_accept_profile sg )) (PreH18 : (kernel_tcb_stack_field_layout sg )) (PreH19 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH20 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH21 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH22 : (pe <> 0)) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)
.

Definition OSMboxPend_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (timeout_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (timeout_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_query_public_slot before eid observed )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (timeout_pre = ticks)) (PreH14 : (perr_pre = pd)) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (sem_pend_profile sg )) (PreH17 : (mbox_accept_profile sg )) (PreH18 : (kernel_tcb_stack_field_layout sg )) (PreH19 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH20 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH21 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH22 : (pe <> 0)) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))
.

Definition OSMboxPend_entail_wit_2 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ”
  &&  emp
).

Definition OSMboxPend_entail_wit_2_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (((before.(IntrState) ).(intNesting) ) <= 255)
.

Definition OSMboxPend_entail_wit_2_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= ((before.(IntrState) ).(intNesting) ))
.

Definition OSMboxPend_entail_wit_3 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ”
  &&  emp
).

Definition OSMboxPend_entail_wit_3_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (((before.(IntrState) ).(lockNesting) ) <= 255)
.

Definition OSMboxPend_entail_wit_3_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= ((before.(IntrState) ).(lockNesting) ))
.

Definition OSMboxPend_entail_wit_4 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((mbox_message_ptr (mailbox)) = 0)) (PreH3 : (environment = (Some (owned)))) (PreH4 : (external = (task_stack_call_external (owned)))) (PreH5 : (platform = (task_stack_call_platform (owned)))) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH7 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH8 : ((mbox_message_ptr (mailbox)) = 0)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (mbox_pend_api_prefix pe before eid )) (PreH11 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH12 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH14 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH15 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH21 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH23 : (timeout_pre <= UINT_MAX)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (timeout_pre >= 0)) (PreH26 : (0 >= 0)) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (valid_event_id sg eid )) (PreH31 : (q_query_public_slot before eid observed )) (PreH32 : (UCOS2_state_inv sg before )) (PreH33 : (pevent_pre <> 0)) (PreH34 : (pevent_pre = pe)) (PreH35 : (timeout_pre = ticks)) (PreH36 : (perr_pre = pd)) (PreH37 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH38 : (sem_pend_profile sg )) (PreH39 : (mbox_accept_profile sg )) (PreH40 : (kernel_tcb_stack_field_layout sg )) (PreH41 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH42 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH43 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH44 : (pe <> 0)) (PreH45 : (event_object_layout_prop sg eid )) (PreH46 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH47 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((old.(dly) ) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (ticks <= UINT_MAX)) (PreH4 : ((old.(dly) ) >= 0)) (PreH5 : (retval >= 0)) (PreH6 : (ticks >= 0)) (PreH7 : ((mbox_message_ptr (mailbox)) = 0)) (PreH8 : (environment = (Some (owned)))) (PreH9 : (external = (task_stack_call_external (owned)))) (PreH10 : (platform = (task_stack_call_platform (owned)))) (PreH11 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : ((mbox_message_ptr (mailbox)) = 0)) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (mbox_pend_api_prefix pe before eid )) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH18 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH20 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH21 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH26 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH28 : (timeout_pre <= UINT_MAX)) (PreH29 : (0 <= UINT_MAX)) (PreH30 : (timeout_pre >= 0)) (PreH31 : (0 >= 0)) (PreH32 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (pe = (event_addr (sg) (eid)))) (PreH35 : (valid_event_id sg eid )) (PreH36 : (q_query_public_slot before eid observed )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (pevent_pre <> 0)) (PreH39 : (pevent_pre = pe)) (PreH40 : (timeout_pre = ticks)) (PreH41 : (perr_pre = pd)) (PreH42 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH43 : (sem_pend_profile sg )) (PreH44 : (mbox_accept_profile sg )) (PreH45 : (kernel_tcb_stack_field_layout sg )) (PreH46 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH48 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH49 : (pe <> 0)) (PreH50 : (event_object_layout_prop sg eid )) (PreH51 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH52 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ”
  &&  emp
).

Definition OSMboxPend_entail_wit_4_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((old.(dly) ) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (ticks <= UINT_MAX)) (PreH4 : ((old.(dly) ) >= 0)) (PreH5 : (retval >= 0)) (PreH6 : (ticks >= 0)) (PreH7 : ((mbox_message_ptr (mailbox)) = 0)) (PreH8 : (environment = (Some (owned)))) (PreH9 : (external = (task_stack_call_external (owned)))) (PreH10 : (platform = (task_stack_call_platform (owned)))) (PreH11 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : ((mbox_message_ptr (mailbox)) = 0)) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (mbox_pend_api_prefix pe before eid )) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH18 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH20 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH21 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH26 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH28 : (timeout_pre <= UINT_MAX)) (PreH29 : (0 <= UINT_MAX)) (PreH30 : (timeout_pre >= 0)) (PreH31 : (0 >= 0)) (PreH32 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (pe = (event_addr (sg) (eid)))) (PreH35 : (valid_event_id sg eid )) (PreH36 : (q_query_public_slot before eid observed )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (pevent_pre <> 0)) (PreH39 : (pevent_pre = pe)) (PreH40 : (timeout_pre = ticks)) (PreH41 : (perr_pre = pd)) (PreH42 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH43 : (sem_pend_profile sg )) (PreH44 : (mbox_accept_profile sg )) (PreH45 : (kernel_tcb_stack_field_layout sg )) (PreH46 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH48 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH49 : (pe <> 0)) (PreH50 : (event_object_layout_prop sg eid )) (PreH51 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH52 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((encode_task_status ((old.(stat) ))) <= 255)
.

Definition OSMboxPend_entail_wit_4_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((old.(dly) ) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (ticks <= UINT_MAX)) (PreH4 : ((old.(dly) ) >= 0)) (PreH5 : (retval >= 0)) (PreH6 : (ticks >= 0)) (PreH7 : ((mbox_message_ptr (mailbox)) = 0)) (PreH8 : (environment = (Some (owned)))) (PreH9 : (external = (task_stack_call_external (owned)))) (PreH10 : (platform = (task_stack_call_platform (owned)))) (PreH11 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : ((mbox_message_ptr (mailbox)) = 0)) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (mbox_pend_api_prefix pe before eid )) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH18 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH20 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH21 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH26 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH28 : (timeout_pre <= UINT_MAX)) (PreH29 : (0 <= UINT_MAX)) (PreH30 : (timeout_pre >= 0)) (PreH31 : (0 >= 0)) (PreH32 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (pe = (event_addr (sg) (eid)))) (PreH35 : (valid_event_id sg eid )) (PreH36 : (q_query_public_slot before eid observed )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (pevent_pre <> 0)) (PreH39 : (pevent_pre = pe)) (PreH40 : (timeout_pre = ticks)) (PreH41 : (perr_pre = pd)) (PreH42 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH43 : (sem_pend_profile sg )) (PreH44 : (mbox_accept_profile sg )) (PreH45 : (kernel_tcb_stack_field_layout sg )) (PreH46 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH48 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH49 : (pe <> 0)) (PreH50 : (event_object_layout_prop sg eid )) (PreH51 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH52 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (encode_task_status ((old.(stat) ))))
.

Definition OSMboxPend_entail_wit_5_1 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval_2 <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval_2 >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 = (encode_pend_status ((node.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 resume_entry_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid_2)))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry_2 resume_tid_2 node )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (code: Z)  (cleaning: UCOS2_Verify_State)  (resume_tid: Z)  (node_2: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid (encode_msg ((node.(msg) ))) code cleaning resume_tid node_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node_2.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node_2.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node_2.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node_2.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node_2 )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval_2 <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval_2 >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 = (encode_pend_status ((node.(statPend) ))))) ,
  TT && emp 
|--
  “ (q_pend_cleanup_observation sg resume_entry_2 eid (encode_msg ((node.(msg) ))) 0 resume_entry_2 resume_tid_2 node ) ”
  &&  emp
).

Definition OSMboxPend_entail_wit_5_1_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval_2 <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval_2 >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 = (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_cleanup_observation sg resume_entry_2 eid (encode_msg ((node.(msg) ))) 0 resume_entry_2 resume_tid_2 node )
.

Definition OSMboxPend_entail_wit_5_2 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval_2 <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval_2 >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH69 : (2 = (encode_pend_status ((node_2.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 resume_entry_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid_2)))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node_2.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node_2.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node_2.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node_2.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry_2 resume_tid_2 node_2 )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 14)
|--
  EX (code: Z)  (cleaning: UCOS2_Verify_State)  (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid 0 code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval_2 <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval_2 >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH69 : (2 = (encode_pend_status ((node_2.(statPend) ))))) ,
  TT && emp 
|--
  “ (q_pend_cleanup_observation sg resume_entry_2 eid 0 14 resume_entry_2 resume_tid_2 node_2 ) ”
  &&  emp
).

Definition OSMboxPend_entail_wit_5_2_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval_2 <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval_2 >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH69 : (2 = (encode_pend_status ((node_2.(statPend) ))))) ,
  (q_pend_cleanup_observation sg resume_entry_2 eid 0 14 resume_entry_2 resume_tid_2 node_2 )
.

Definition OSMboxPend_entail_wit_5_3 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning_2: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry_2 eid 0 10 cleaning_2 resume_tid_2 cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : ((node_2.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry_2 eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH9 : (interrupt_saved_value mask retval )) (PreH10 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH11 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (environment = (Some (owned_2)))) (PreH14 : (external = (task_stack_call_external (owned_2)))) (PreH15 : (platform = (task_stack_call_platform (owned_2)))) (PreH16 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH17 : (mbox_pend_sched_admitted environment critical )) (PreH18 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH19 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH20 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH21 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH22 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH23 : ((old.(dly) ) <= UINT_MAX)) (PreH24 : (retval_2 <= UINT_MAX)) (PreH25 : (ticks <= UINT_MAX)) (PreH26 : ((old.(dly) ) >= 0)) (PreH27 : (retval_2 >= 0)) (PreH28 : (ticks >= 0)) (PreH29 : ((mbox_message_ptr (mailbox)) = 0)) (PreH30 : (environment = (Some (owned)))) (PreH31 : (external = (task_stack_call_external (owned)))) (PreH32 : (platform = (task_stack_call_platform (owned)))) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH35 : ((mbox_message_ptr (mailbox)) = 0)) (PreH36 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (mbox_pend_api_prefix pe before eid )) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH39 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH40 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH42 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH43 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH44 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH48 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH49 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH50 : (timeout_pre <= UINT_MAX)) (PreH51 : (0 <= UINT_MAX)) (PreH52 : (timeout_pre >= 0)) (PreH53 : (0 >= 0)) (PreH54 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH55 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH56 : (pe = (event_addr (sg) (eid)))) (PreH57 : (valid_event_id sg eid )) (PreH58 : (q_query_public_slot before eid observed )) (PreH59 : (UCOS2_state_inv sg before )) (PreH60 : (pevent_pre <> 0)) (PreH61 : (pevent_pre = pe)) (PreH62 : (timeout_pre = ticks)) (PreH63 : (perr_pre = pd)) (PreH64 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH65 : (sem_pend_profile sg )) (PreH66 : (mbox_accept_profile sg )) (PreH67 : (kernel_tcb_stack_field_layout sg )) (PreH68 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH69 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH70 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH71 : (pe <> 0)) (PreH72 : (event_object_layout_prop sg eid )) (PreH73 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH74 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH75 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH76 : (2 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH77 : (1 = (encode_pend_status ((node_2.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 cleaning_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid_2)))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning_2 resume_tid_2 cleaned_node )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 10)
|--
  EX (code: Z)  (cleaning: UCOS2_Verify_State)  (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid 0 code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
.

Definition OSMboxPend_entail_wit_5_4 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning_2: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry_2 eid 0 10 cleaning_2 resume_tid_2 cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : ((node_2.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry_2 eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH9 : (interrupt_saved_value mask retval )) (PreH10 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH11 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (environment = (Some (owned_2)))) (PreH14 : (external = (task_stack_call_external (owned_2)))) (PreH15 : (platform = (task_stack_call_platform (owned_2)))) (PreH16 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH17 : (mbox_pend_sched_admitted environment critical )) (PreH18 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH19 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH20 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH21 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH22 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH23 : ((old.(dly) ) <= UINT_MAX)) (PreH24 : (retval_2 <= UINT_MAX)) (PreH25 : (ticks <= UINT_MAX)) (PreH26 : ((old.(dly) ) >= 0)) (PreH27 : (retval_2 >= 0)) (PreH28 : (ticks >= 0)) (PreH29 : ((mbox_message_ptr (mailbox)) = 0)) (PreH30 : (environment = (Some (owned)))) (PreH31 : (external = (task_stack_call_external (owned)))) (PreH32 : (platform = (task_stack_call_platform (owned)))) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH35 : ((mbox_message_ptr (mailbox)) = 0)) (PreH36 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH37 : (mbox_pend_api_prefix pe before eid )) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH39 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH40 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH42 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH43 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH44 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH48 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH49 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH50 : (timeout_pre <= UINT_MAX)) (PreH51 : (0 <= UINT_MAX)) (PreH52 : (timeout_pre >= 0)) (PreH53 : (0 >= 0)) (PreH54 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH55 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH56 : (pe = (event_addr (sg) (eid)))) (PreH57 : (valid_event_id sg eid )) (PreH58 : (q_query_public_slot before eid observed )) (PreH59 : (UCOS2_state_inv sg before )) (PreH60 : (pevent_pre <> 0)) (PreH61 : (pevent_pre = pe)) (PreH62 : (timeout_pre = ticks)) (PreH63 : (perr_pre = pd)) (PreH64 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH65 : (sem_pend_profile sg )) (PreH66 : (mbox_accept_profile sg )) (PreH67 : (kernel_tcb_stack_field_layout sg )) (PreH68 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH69 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH70 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH71 : (pe <> 0)) (PreH72 : (event_object_layout_prop sg eid )) (PreH73 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH74 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH75 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH76 : (2 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH77 : (1 <> (encode_pend_status ((node_2.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 cleaning_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid_2)))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid_2)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning_2 resume_tid_2 cleaned_node )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 10)
|--
  EX (code: Z)  (cleaning: UCOS2_Verify_State)  (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid 0 code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
.

Definition OSMboxPend_return_wit_1 := 
(
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before pmsg X )
) \/
(
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before pmsg X )
).

Definition OSMboxPend_return_wit_1_split_goal_spatial := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before pmsg X )
.

Definition OSMboxPend_return_wit_2 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint )) (PreH2 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before (mbox_message_ptr (mailbox)) X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint )) (PreH2 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before (mbox_message_ptr (mailbox)) X )
).

Definition OSMboxPend_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint )) (PreH2 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before (mbox_message_ptr (mailbox)) X )
.

Definition OSMboxPend_return_wit_3 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (mbox_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (mbox_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSMboxPend_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (mbox_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSMboxPend_return_wit_4 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSMboxPend_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (mbox_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSMboxPend_return_wit_5 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (mbox_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (mbox_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSMboxPend_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (mbox_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSMboxPend_return_wit_6 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSMboxPend_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (mbox_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSMboxPend_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe <> 0)) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ”
.

Definition OSMboxPend_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe <> 0)) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_1 := OSMboxPend_partial_solve_wit_1_pure -> OSMboxPend_partial_solve_wit_1_aux.

Definition OSMboxPend_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (mbox_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ”
.

Definition OSMboxPend_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (mbox_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_2 := OSMboxPend_partial_solve_wit_2_pure -> OSMboxPend_partial_solve_wit_2_aux.

Definition OSMboxPend_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (mbox_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSMboxPend_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (mbox_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_3 := OSMboxPend_partial_solve_wit_3_pure -> OSMboxPend_partial_solve_wit_3_aux.

Definition OSMboxPend_partial_solve_wit_4 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (mbox_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_input (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_save_input (MboxPendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (mbox_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_output (MboxPendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSMboxPend_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (mbox_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_output (MboxPendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_save_output (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_5 := OSMboxPend_partial_solve_wit_5_pure -> OSMboxPend_partial_solve_wit_5_aux.

Definition OSMboxPend_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mailbox: MboxFields) (PreH1 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mbox_message_ptr (mailbox)) = (mbox_message_ptr (mailbox))) ” 
  &&  “ ((mbox_message_ptr (mailbox)) <> 0) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ”
.

Definition OSMboxPend_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mailbox: MboxFields) (PreH1 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mbox_message_ptr (mailbox)) = (mbox_message_ptr (mailbox))) ” 
  &&  “ ((mbox_message_ptr (mailbox)) <> 0) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) <> 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_6 := OSMboxPend_partial_solve_wit_6_pure -> OSMboxPend_partial_solve_wit_6_aux.

Definition OSMboxPend_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint )) (PreH3 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (mbox_pend_api_prefix pe before eid )) (PreH6 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH8 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH9 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH10 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH11 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH16 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH18 : (timeout_pre <= UINT_MAX)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (timeout_pre >= 0)) (PreH21 : (0 >= 0)) (PreH22 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH23 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (valid_event_id sg eid )) (PreH26 : (q_query_public_slot before eid observed )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (timeout_pre = ticks)) (PreH31 : (perr_pre = pd)) (PreH32 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH33 : (sem_pend_profile sg )) (PreH34 : (mbox_accept_profile sg )) (PreH35 : (kernel_tcb_stack_field_layout sg )) (PreH36 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH37 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH38 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH39 : (pe <> 0)) (PreH40 : (event_object_layout_prop sg eid )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMboxPend_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint )) (PreH3 : ((mbox_message_ptr (mailbox)) <> 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (mbox_pend_api_prefix pe before eid )) (PreH6 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH8 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH9 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH10 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH11 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH16 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH18 : (timeout_pre <= UINT_MAX)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (timeout_pre >= 0)) (PreH21 : (0 >= 0)) (PreH22 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH23 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (valid_event_id sg eid )) (PreH26 : (q_query_public_slot before eid observed )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (timeout_pre = ticks)) (PreH31 : (perr_pre = pd)) (PreH32 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH33 : (sem_pend_profile sg )) (PreH34 : (mbox_accept_profile sg )) (PreH35 : (kernel_tcb_stack_field_layout sg )) (PreH36 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH37 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH38 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH39 : (pe <> 0)) (PreH40 : (event_object_layout_prop sg eid )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks (mbox_message_ptr (mailbox)) checkpoint ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) <> 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_7 := OSMboxPend_partial_solve_wit_7_pure -> OSMboxPend_partial_solve_wit_7_aux.

Definition OSMboxPend_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mailbox: MboxFields) (PreH1 : ((mbox_message_ptr (mailbox)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mbox_message_ptr (mailbox)) = (mbox_message_ptr (mailbox))) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mailbox: MboxFields) (PreH1 : ((mbox_message_ptr (mailbox)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (mbox_pend_api_prefix pe before eid )) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH6 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (timeout_pre <= UINT_MAX)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (timeout_pre >= 0)) (PreH20 : (0 >= 0)) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_query_public_slot before eid observed )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (timeout_pre = ticks)) (PreH30 : (perr_pre = pd)) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (sem_pend_profile sg )) (PreH33 : (mbox_accept_profile sg )) (PreH34 : (kernel_tcb_stack_field_layout sg )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH37 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH38 : (pe <> 0)) (PreH39 : (event_object_layout_prop sg eid )) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mbox_message_ptr (mailbox)) = (mbox_message_ptr (mailbox))) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask retval pe before entry eid observed current mailbox )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_8 := OSMboxPend_partial_solve_wit_8_pure -> OSMboxPend_partial_solve_wit_8_aux.

Definition OSMboxPend_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH2 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH3 : ((old.(dly) ) <= UINT_MAX)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (ticks <= UINT_MAX)) (PreH6 : ((old.(dly) ) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (ticks >= 0)) (PreH9 : ((mbox_message_ptr (mailbox)) = 0)) (PreH10 : (environment = (Some (owned)))) (PreH11 : (external = (task_stack_call_external (owned)))) (PreH12 : (platform = (task_stack_call_platform (owned)))) (PreH13 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH14 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH15 : ((mbox_message_ptr (mailbox)) = 0)) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (mbox_pend_api_prefix pe before eid )) (PreH18 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH19 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH21 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH28 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH30 : (timeout_pre <= UINT_MAX)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (timeout_pre >= 0)) (PreH33 : (0 >= 0)) (PreH34 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (pe = (event_addr (sg) (eid)))) (PreH37 : (valid_event_id sg eid )) (PreH38 : (q_query_public_slot before eid observed )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : (pevent_pre <> 0)) (PreH41 : (pevent_pre = pe)) (PreH42 : (timeout_pre = ticks)) (PreH43 : (perr_pre = pd)) (PreH44 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH45 : (sem_pend_profile sg )) (PreH46 : (mbox_accept_profile sg )) (PreH47 : (kernel_tcb_stack_field_layout sg )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH50 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH51 : (pe <> 0)) (PreH52 : (event_object_layout_prop sg eid )) (PreH53 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH54 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSMboxPend_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH2 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH3 : ((old.(dly) ) <= UINT_MAX)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (ticks <= UINT_MAX)) (PreH6 : ((old.(dly) ) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (ticks >= 0)) (PreH9 : ((mbox_message_ptr (mailbox)) = 0)) (PreH10 : (environment = (Some (owned)))) (PreH11 : (external = (task_stack_call_external (owned)))) (PreH12 : (platform = (task_stack_call_platform (owned)))) (PreH13 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH14 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH15 : ((mbox_message_ptr (mailbox)) = 0)) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (mbox_pend_api_prefix pe before eid )) (PreH18 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH19 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH21 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH28 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH30 : (timeout_pre <= UINT_MAX)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (timeout_pre >= 0)) (PreH33 : (0 >= 0)) (PreH34 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH35 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH36 : (pe = (event_addr (sg) (eid)))) (PreH37 : (valid_event_id sg eid )) (PreH38 : (q_query_public_slot before eid observed )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : (pevent_pre <> 0)) (PreH41 : (pevent_pre = pe)) (PreH42 : (timeout_pre = ticks)) (PreH43 : (perr_pre = pd)) (PreH44 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH45 : (sem_pend_profile sg )) (PreH46 : (mbox_accept_profile sg )) (PreH47 : (kernel_tcb_stack_field_layout sg )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH50 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH51 : (pe <> 0)) (PreH52 : (event_object_layout_prop sg eid )) (PreH53 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH54 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_9 := OSMboxPend_partial_solve_wit_9_pure -> OSMboxPend_partial_solve_wit_9_aux.

Definition OSMboxPend_partial_solve_wit_10_pure := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ”
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : ((mbox_message_ptr (mailbox)) = 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (mbox_pend_api_prefix pe before eid )) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH24 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH30 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH32 : (timeout_pre <= UINT_MAX)) (PreH33 : (0 <= UINT_MAX)) (PreH34 : (timeout_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (pe = (event_addr (sg) (eid)))) (PreH39 : (valid_event_id sg eid )) (PreH40 : (q_query_public_slot before eid observed )) (PreH41 : (UCOS2_state_inv sg before )) (PreH42 : (pevent_pre <> 0)) (PreH43 : (pevent_pre = pe)) (PreH44 : (timeout_pre = ticks)) (PreH45 : (perr_pre = pd)) (PreH46 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH47 : (sem_pend_profile sg )) (PreH48 : (mbox_accept_profile sg )) (PreH49 : (kernel_tcb_stack_field_layout sg )) (PreH50 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH51 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH52 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH53 : (pe <> 0)) (PreH54 : (event_object_layout_prop sg eid )) (PreH55 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH56 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ”
).

Definition OSMboxPend_partial_solve_wit_10_pure_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : ((mbox_message_ptr (mailbox)) = 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (mbox_pend_api_prefix pe before eid )) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH24 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH30 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH32 : (timeout_pre <= UINT_MAX)) (PreH33 : (0 <= UINT_MAX)) (PreH34 : (timeout_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (pe = (event_addr (sg) (eid)))) (PreH39 : (valid_event_id sg eid )) (PreH40 : (q_query_public_slot before eid observed )) (PreH41 : (UCOS2_state_inv sg before )) (PreH42 : (pevent_pre <> 0)) (PreH43 : (pevent_pre = pe)) (PreH44 : (timeout_pre = ticks)) (PreH45 : (perr_pre = pd)) (PreH46 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH47 : (sem_pend_profile sg )) (PreH48 : (mbox_accept_profile sg )) (PreH49 : (kernel_tcb_stack_field_layout sg )) (PreH50 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH51 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH52 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH53 : (pe <> 0)) (PreH54 : (event_object_layout_prop sg eid )) (PreH55 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH56 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ”
.

Definition OSMboxPend_partial_solve_wit_10_pure_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : ((mbox_message_ptr (mailbox)) = 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (mbox_pend_api_prefix pe before eid )) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH24 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH30 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH32 : (timeout_pre <= UINT_MAX)) (PreH33 : (0 <= UINT_MAX)) (PreH34 : (timeout_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (pe = (event_addr (sg) (eid)))) (PreH39 : (valid_event_id sg eid )) (PreH40 : (q_query_public_slot before eid observed )) (PreH41 : (UCOS2_state_inv sg before )) (PreH42 : (pevent_pre <> 0)) (PreH43 : (pevent_pre = pe)) (PreH44 : (timeout_pre = ticks)) (PreH45 : (perr_pre = pd)) (PreH46 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH47 : (sem_pend_profile sg )) (PreH48 : (mbox_accept_profile sg )) (PreH49 : (kernel_tcb_stack_field_layout sg )) (PreH50 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH51 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH52 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH53 : (pe <> 0)) (PreH54 : (event_object_layout_prop sg eid )) (PreH55 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH56 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ”
.

Definition OSMboxPend_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_10 := OSMboxPend_partial_solve_wit_10_pure -> OSMboxPend_partial_solve_wit_10_aux.

Definition OSMboxPend_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : ((mbox_message_ptr (mailbox)) = 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (mbox_pend_api_prefix pe before eid )) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH24 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH30 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH32 : (timeout_pre <= UINT_MAX)) (PreH33 : (0 <= UINT_MAX)) (PreH34 : (timeout_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (pe = (event_addr (sg) (eid)))) (PreH39 : (valid_event_id sg eid )) (PreH40 : (q_query_public_slot before eid observed )) (PreH41 : (UCOS2_state_inv sg before )) (PreH42 : (pevent_pre <> 0)) (PreH43 : (pevent_pre = pe)) (PreH44 : (timeout_pre = ticks)) (PreH45 : (perr_pre = pd)) (PreH46 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH47 : (sem_pend_profile sg )) (PreH48 : (mbox_accept_profile sg )) (PreH49 : (kernel_tcb_stack_field_layout sg )) (PreH50 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH51 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH52 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH53 : (pe <> 0)) (PreH54 : (event_object_layout_prop sg eid )) (PreH55 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH56 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_wait_call_post sg entry eid current tid old ticks )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
.

Definition OSMboxPend_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : ((mbox_message_ptr (mailbox)) = 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (mbox_pend_api_prefix pe before eid )) (PreH20 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH23 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH24 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH30 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH32 : (timeout_pre <= UINT_MAX)) (PreH33 : (0 <= UINT_MAX)) (PreH34 : (timeout_pre >= 0)) (PreH35 : (0 >= 0)) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (pe = (event_addr (sg) (eid)))) (PreH39 : (valid_event_id sg eid )) (PreH40 : (q_query_public_slot before eid observed )) (PreH41 : (UCOS2_state_inv sg before )) (PreH42 : (pevent_pre <> 0)) (PreH43 : (pevent_pre = pe)) (PreH44 : (timeout_pre = ticks)) (PreH45 : (perr_pre = pd)) (PreH46 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH47 : (sem_pend_profile sg )) (PreH48 : (mbox_accept_profile sg )) (PreH49 : (kernel_tcb_stack_field_layout sg )) (PreH50 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH51 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH52 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH53 : (pe <> 0)) (PreH54 : (event_object_layout_prop sg eid )) (PreH55 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH56 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_wait_call_post sg entry eid current tid old ticks )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  (mbox_pend_wait_call_post sg entry eid current tid old ticks )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_11 := OSMboxPend_partial_solve_wit_11_pure -> OSMboxPend_partial_solve_wit_11_aux.

Definition OSMboxPend_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH2 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_restore_input (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask retval entry waiting )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMboxPend_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH2 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_input (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask retval entry waiting )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_restore_input (Some ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask retval entry waiting )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_12 := OSMboxPend_partial_solve_wit_12_pure -> OSMboxPend_partial_solve_wit_12_aux.

Definition OSMboxPend_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH2 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output (Some ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask waiting )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ”
.

Definition OSMboxPend_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH2 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : ((mbox_message_ptr (mailbox)) = 0)) (PreH13 : (environment = (Some (owned)))) (PreH14 : (external = (task_stack_call_external (owned)))) (PreH15 : (platform = (task_stack_call_platform (owned)))) (PreH16 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (mbox_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (mbox_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_restore_output (Some ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask waiting )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_restore_output (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask waiting )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_13 := OSMboxPend_partial_solve_wit_13_pure -> OSMboxPend_partial_solve_wit_13_aux.

Definition OSMboxPend_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (PreH1 : (environment = (Some (owned_2)))) (PreH2 : (external = (task_stack_call_external (owned_2)))) (PreH3 : (platform = (task_stack_call_platform (owned_2)))) (PreH4 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH5 : (mbox_pend_sched_admitted environment critical )) (PreH6 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH7 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH8 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH9 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH10 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH11 : ((old.(dly) ) <= UINT_MAX)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (ticks <= UINT_MAX)) (PreH14 : ((old.(dly) ) >= 0)) (PreH15 : (retval >= 0)) (PreH16 : (ticks >= 0)) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (environment = (Some (owned)))) (PreH19 : (external = (task_stack_call_external (owned)))) (PreH20 : (platform = (task_stack_call_platform (owned)))) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH23 : ((mbox_message_ptr (mailbox)) = 0)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (mbox_pend_api_prefix pe before eid )) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH27 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH36 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH38 : (timeout_pre <= UINT_MAX)) (PreH39 : (0 <= UINT_MAX)) (PreH40 : (timeout_pre >= 0)) (PreH41 : (0 >= 0)) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (pe = (event_addr (sg) (eid)))) (PreH45 : (valid_event_id sg eid )) (PreH46 : (q_query_public_slot before eid observed )) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : (pevent_pre <> 0)) (PreH49 : (pevent_pre = pe)) (PreH50 : (timeout_pre = ticks)) (PreH51 : (perr_pre = pd)) (PreH52 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH53 : (sem_pend_profile sg )) (PreH54 : (mbox_accept_profile sg )) (PreH55 : (kernel_tcb_stack_field_layout sg )) (PreH56 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH57 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH58 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH59 : (pe <> 0)) (PreH60 : (event_object_layout_prop sg eid )) (PreH61 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH62 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_sched_continuation_phase_sched_input (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg released mask unmasked )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSMboxPend_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (PreH1 : (environment = (Some (owned_2)))) (PreH2 : (external = (task_stack_call_external (owned_2)))) (PreH3 : (platform = (task_stack_call_platform (owned_2)))) (PreH4 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH5 : (mbox_pend_sched_admitted environment critical )) (PreH6 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH7 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH8 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH9 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH10 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH11 : ((old.(dly) ) <= UINT_MAX)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (ticks <= UINT_MAX)) (PreH14 : ((old.(dly) ) >= 0)) (PreH15 : (retval >= 0)) (PreH16 : (ticks >= 0)) (PreH17 : ((mbox_message_ptr (mailbox)) = 0)) (PreH18 : (environment = (Some (owned)))) (PreH19 : (external = (task_stack_call_external (owned)))) (PreH20 : (platform = (task_stack_call_platform (owned)))) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH23 : ((mbox_message_ptr (mailbox)) = 0)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (mbox_pend_api_prefix pe before eid )) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH27 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH36 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH38 : (timeout_pre <= UINT_MAX)) (PreH39 : (0 <= UINT_MAX)) (PreH40 : (timeout_pre >= 0)) (PreH41 : (0 >= 0)) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (pe = (event_addr (sg) (eid)))) (PreH45 : (valid_event_id sg eid )) (PreH46 : (q_query_public_slot before eid observed )) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : (pevent_pre <> 0)) (PreH49 : (pevent_pre = pe)) (PreH50 : (timeout_pre = ticks)) (PreH51 : (perr_pre = pd)) (PreH52 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH53 : (sem_pend_profile sg )) (PreH54 : (mbox_accept_profile sg )) (PreH55 : (kernel_tcb_stack_field_layout sg )) (PreH56 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH57 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH58 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH59 : (pe <> 0)) (PreH60 : (event_object_layout_prop sg eid )) (PreH61 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH62 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_sched_continuation_phase_sched_input (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_sched_continuation_phase_sched_input (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_14 := OSMboxPend_partial_solve_wit_14_pure -> OSMboxPend_partial_solve_wit_14_aux.

Definition OSMboxPend_partial_solve_wit_15_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned_2: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (environment = (Some (owned)))) (PreH3 : (external = (task_stack_call_external (owned)))) (PreH4 : (platform = (task_stack_call_platform (owned)))) (PreH5 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH6 : (mbox_pend_sched_admitted environment critical )) (PreH7 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH8 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH9 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH10 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH11 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH12 : ((old.(dly) ) <= UINT_MAX)) (PreH13 : (retval <= UINT_MAX)) (PreH14 : (ticks <= UINT_MAX)) (PreH15 : ((old.(dly) ) >= 0)) (PreH16 : (retval >= 0)) (PreH17 : (ticks >= 0)) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (environment = (Some (owned_2)))) (PreH20 : (external = (task_stack_call_external (owned_2)))) (PreH21 : (platform = (task_stack_call_platform (owned_2)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((mbox_message_ptr (mailbox)) = 0)) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (mbox_pend_api_prefix pe before eid )) (PreH27 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH28 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH30 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH31 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH37 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH39 : (timeout_pre <= UINT_MAX)) (PreH40 : (0 <= UINT_MAX)) (PreH41 : (timeout_pre >= 0)) (PreH42 : (0 >= 0)) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH45 : (pe = (event_addr (sg) (eid)))) (PreH46 : (valid_event_id sg eid )) (PreH47 : (q_query_public_slot before eid observed )) (PreH48 : (UCOS2_state_inv sg before )) (PreH49 : (pevent_pre <> 0)) (PreH50 : (pevent_pre = pe)) (PreH51 : (timeout_pre = ticks)) (PreH52 : (perr_pre = pd)) (PreH53 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH54 : (sem_pend_profile sg )) (PreH55 : (mbox_accept_profile sg )) (PreH56 : (kernel_tcb_stack_field_layout sg )) (PreH57 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH58 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH59 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH60 : (pe <> 0)) (PreH61 : (event_object_layout_prop sg eid )) (PreH62 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH63 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_sched_continuation_phase_sched_output (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ”
.

Definition OSMboxPend_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned_2: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (environment = (Some (owned)))) (PreH3 : (external = (task_stack_call_external (owned)))) (PreH4 : (platform = (task_stack_call_platform (owned)))) (PreH5 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH6 : (mbox_pend_sched_admitted environment critical )) (PreH7 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH8 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH9 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH10 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH11 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH12 : ((old.(dly) ) <= UINT_MAX)) (PreH13 : (retval <= UINT_MAX)) (PreH14 : (ticks <= UINT_MAX)) (PreH15 : ((old.(dly) ) >= 0)) (PreH16 : (retval >= 0)) (PreH17 : (ticks >= 0)) (PreH18 : ((mbox_message_ptr (mailbox)) = 0)) (PreH19 : (environment = (Some (owned_2)))) (PreH20 : (external = (task_stack_call_external (owned_2)))) (PreH21 : (platform = (task_stack_call_platform (owned_2)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((mbox_message_ptr (mailbox)) = 0)) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (mbox_pend_api_prefix pe before eid )) (PreH27 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH28 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH30 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH31 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH37 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH39 : (timeout_pre <= UINT_MAX)) (PreH40 : (0 <= UINT_MAX)) (PreH41 : (timeout_pre >= 0)) (PreH42 : (0 >= 0)) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH45 : (pe = (event_addr (sg) (eid)))) (PreH46 : (valid_event_id sg eid )) (PreH47 : (q_query_public_slot before eid observed )) (PreH48 : (UCOS2_state_inv sg before )) (PreH49 : (pevent_pre <> 0)) (PreH50 : (pevent_pre = pe)) (PreH51 : (timeout_pre = ticks)) (PreH52 : (perr_pre = pd)) (PreH53 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH54 : (sem_pend_profile sg )) (PreH55 : (mbox_accept_profile sg )) (PreH56 : (kernel_tcb_stack_field_layout sg )) (PreH57 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH58 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH59 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH60 : (pe <> 0)) (PreH61 : (event_object_layout_prop sg eid )) (PreH62 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH63 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_sched_continuation_phase_sched_output (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_sched_continuation_phase_sched_output (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_15 := OSMboxPend_partial_solve_wit_15_pure -> OSMboxPend_partial_solve_wit_15_aux.

Definition OSMboxPend_partial_solve_wit_16 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (PreH1 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (environment = (Some (owned_2)))) (PreH4 : (external = (task_stack_call_external (owned_2)))) (PreH5 : (platform = (task_stack_call_platform (owned_2)))) (PreH6 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH7 : (mbox_pend_sched_admitted environment critical )) (PreH8 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH9 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : ((mbox_message_ptr (mailbox)) = 0)) (PreH20 : (environment = (Some (owned)))) (PreH21 : (external = (task_stack_call_external (owned)))) (PreH22 : (platform = (task_stack_call_platform (owned)))) (PreH23 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH24 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH25 : ((mbox_message_ptr (mailbox)) = 0)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (mbox_pend_api_prefix pe before eid )) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH29 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH30 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH33 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH38 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH39 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH40 : (timeout_pre <= UINT_MAX)) (PreH41 : (0 <= UINT_MAX)) (PreH42 : (timeout_pre >= 0)) (PreH43 : (0 >= 0)) (PreH44 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH45 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH46 : (pe = (event_addr (sg) (eid)))) (PreH47 : (valid_event_id sg eid )) (PreH48 : (q_query_public_slot before eid observed )) (PreH49 : (UCOS2_state_inv sg before )) (PreH50 : (pevent_pre <> 0)) (PreH51 : (pevent_pre = pe)) (PreH52 : (timeout_pre = ticks)) (PreH53 : (perr_pre = pd)) (PreH54 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH55 : (sem_pend_profile sg )) (PreH56 : (mbox_accept_profile sg )) (PreH57 : (kernel_tcb_stack_field_layout sg )) (PreH58 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH59 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH60 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH61 : (pe <> 0)) (PreH62 : (event_object_layout_prop sg eid )) (PreH63 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH64 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_input (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg scheduled mask selected )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_save_input (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg scheduled mask selected )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (environment = (Some (owned_2)))) (PreH4 : (external = (task_stack_call_external (owned_2)))) (PreH5 : (platform = (task_stack_call_platform (owned_2)))) (PreH6 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH7 : (mbox_pend_sched_admitted environment critical )) (PreH8 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH9 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : ((mbox_message_ptr (mailbox)) = 0)) (PreH20 : (environment = (Some (owned)))) (PreH21 : (external = (task_stack_call_external (owned)))) (PreH22 : (platform = (task_stack_call_platform (owned)))) (PreH23 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH24 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH25 : ((mbox_message_ptr (mailbox)) = 0)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (mbox_pend_api_prefix pe before eid )) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH29 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH30 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH33 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH38 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH39 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH40 : (timeout_pre <= UINT_MAX)) (PreH41 : (0 <= UINT_MAX)) (PreH42 : (timeout_pre >= 0)) (PreH43 : (0 >= 0)) (PreH44 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH45 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH46 : (pe = (event_addr (sg) (eid)))) (PreH47 : (valid_event_id sg eid )) (PreH48 : (q_query_public_slot before eid observed )) (PreH49 : (UCOS2_state_inv sg before )) (PreH50 : (pevent_pre <> 0)) (PreH51 : (pevent_pre = pe)) (PreH52 : (timeout_pre = ticks)) (PreH53 : (perr_pre = pd)) (PreH54 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH55 : (sem_pend_profile sg )) (PreH56 : (mbox_accept_profile sg )) (PreH57 : (kernel_tcb_stack_field_layout sg )) (PreH58 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH59 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH60 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH61 : (pe <> 0)) (PreH62 : (event_object_layout_prop sg eid )) (PreH63 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH64 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_output (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg scheduled mask retval_2 selected )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (environment = (Some (owned_2)))) (PreH4 : (external = (task_stack_call_external (owned_2)))) (PreH5 : (platform = (task_stack_call_platform (owned_2)))) (PreH6 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH7 : (mbox_pend_sched_admitted environment critical )) (PreH8 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH9 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : ((mbox_message_ptr (mailbox)) = 0)) (PreH20 : (environment = (Some (owned)))) (PreH21 : (external = (task_stack_call_external (owned)))) (PreH22 : (platform = (task_stack_call_platform (owned)))) (PreH23 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH24 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH25 : ((mbox_message_ptr (mailbox)) = 0)) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (mbox_pend_api_prefix pe before eid )) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH29 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH30 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH33 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH38 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH39 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH40 : (timeout_pre <= UINT_MAX)) (PreH41 : (0 <= UINT_MAX)) (PreH42 : (timeout_pre >= 0)) (PreH43 : (0 >= 0)) (PreH44 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH45 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH46 : (pe = (event_addr (sg) (eid)))) (PreH47 : (valid_event_id sg eid )) (PreH48 : (q_query_public_slot before eid observed )) (PreH49 : (UCOS2_state_inv sg before )) (PreH50 : (pevent_pre <> 0)) (PreH51 : (pevent_pre = pe)) (PreH52 : (timeout_pre = ticks)) (PreH53 : (perr_pre = pd)) (PreH54 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH55 : (sem_pend_profile sg )) (PreH56 : (mbox_accept_profile sg )) (PreH57 : (kernel_tcb_stack_field_layout sg )) (PreH58 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH59 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH60 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH61 : (pe <> 0)) (PreH62 : (event_object_layout_prop sg eid )) (PreH63 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH64 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_save_output (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) (task_stack_call_external (owned_2)) (task_stack_call_platform (owned_2)) (Some (owned_2)) critical saved_local sg scheduled mask retval_2 selected )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_save_output (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg scheduled mask retval_2 selected )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_17 := OSMboxPend_partial_solve_wit_17_pure -> OSMboxPend_partial_solve_wit_17_aux.

Definition OSMboxPend_partial_solve_wit_18_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (environment = (Some (owned_2)))) (PreH12 : (external = (task_stack_call_external (owned_2)))) (PreH13 : (platform = (task_stack_call_platform (owned_2)))) (PreH14 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH15 : (mbox_pend_sched_admitted environment critical )) (PreH16 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH18 : (mbox_pend_wait_entry sg entry eid current_2 tid old )) (PreH19 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH20 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH21 : ((old.(dly) ) <= UINT_MAX)) (PreH22 : (retval <= UINT_MAX)) (PreH23 : (ticks <= UINT_MAX)) (PreH24 : ((old.(dly) ) >= 0)) (PreH25 : (retval >= 0)) (PreH26 : (ticks >= 0)) (PreH27 : ((mbox_message_ptr (mailbox)) = 0)) (PreH28 : (environment = (Some (owned)))) (PreH29 : (external = (task_stack_call_external (owned)))) (PreH30 : (platform = (task_stack_call_platform (owned)))) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH33 : ((mbox_message_ptr (mailbox)) = 0)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (mbox_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (mbox_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (environment = (Some (owned_2)))) (PreH12 : (external = (task_stack_call_external (owned_2)))) (PreH13 : (platform = (task_stack_call_platform (owned_2)))) (PreH14 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH15 : (mbox_pend_sched_admitted environment critical )) (PreH16 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH18 : (mbox_pend_wait_entry sg entry eid current_2 tid old )) (PreH19 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH20 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH21 : ((old.(dly) ) <= UINT_MAX)) (PreH22 : (retval <= UINT_MAX)) (PreH23 : (ticks <= UINT_MAX)) (PreH24 : ((old.(dly) ) >= 0)) (PreH25 : (retval >= 0)) (PreH26 : (ticks >= 0)) (PreH27 : ((mbox_message_ptr (mailbox)) = 0)) (PreH28 : (environment = (Some (owned)))) (PreH29 : (external = (task_stack_call_external (owned)))) (PreH30 : (platform = (task_stack_call_platform (owned)))) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH33 : ((mbox_message_ptr (mailbox)) = 0)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (mbox_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (mbox_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current_2 tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 <> (encode_pend_status ((node.(statPend) )))) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_18 := OSMboxPend_partial_solve_wit_18_pure -> OSMboxPend_partial_solve_wit_18_aux.

Definition OSMboxPend_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (environment = (Some (owned_2)))) (PreH12 : (external = (task_stack_call_external (owned_2)))) (PreH13 : (platform = (task_stack_call_platform (owned_2)))) (PreH14 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH15 : (mbox_pend_sched_admitted environment critical )) (PreH16 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH18 : (mbox_pend_wait_entry sg entry eid current_2 tid old )) (PreH19 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH20 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH21 : ((old.(dly) ) <= UINT_MAX)) (PreH22 : (retval <= UINT_MAX)) (PreH23 : (ticks <= UINT_MAX)) (PreH24 : ((old.(dly) ) >= 0)) (PreH25 : (retval >= 0)) (PreH26 : (ticks >= 0)) (PreH27 : ((mbox_message_ptr (mailbox)) = 0)) (PreH28 : (environment = (Some (owned)))) (PreH29 : (external = (task_stack_call_external (owned)))) (PreH30 : (platform = (task_stack_call_platform (owned)))) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH33 : ((mbox_message_ptr (mailbox)) = 0)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (mbox_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (mbox_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (environment = (Some (owned_2)))) (PreH12 : (external = (task_stack_call_external (owned_2)))) (PreH13 : (platform = (task_stack_call_platform (owned_2)))) (PreH14 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH15 : (mbox_pend_sched_admitted environment critical )) (PreH16 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH18 : (mbox_pend_wait_entry sg entry eid current_2 tid old )) (PreH19 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH20 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH21 : ((old.(dly) ) <= UINT_MAX)) (PreH22 : (retval <= UINT_MAX)) (PreH23 : (ticks <= UINT_MAX)) (PreH24 : ((old.(dly) ) >= 0)) (PreH25 : (retval >= 0)) (PreH26 : (ticks >= 0)) (PreH27 : ((mbox_message_ptr (mailbox)) = 0)) (PreH28 : (environment = (Some (owned)))) (PreH29 : (external = (task_stack_call_external (owned)))) (PreH30 : (platform = (task_stack_call_platform (owned)))) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH33 : ((mbox_message_ptr (mailbox)) = 0)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (mbox_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (mbox_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current_2 tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 = (encode_pend_status ((node.(statPend) )))) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_19 := OSMboxPend_partial_solve_wit_19_pure -> OSMboxPend_partial_solve_wit_19_aux.

Definition OSMboxPend_partial_solve_wit_20 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current_2 )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (environment = (Some (owned_2)))) (PreH12 : (external = (task_stack_call_external (owned_2)))) (PreH13 : (platform = (task_stack_call_platform (owned_2)))) (PreH14 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH15 : (mbox_pend_sched_admitted environment critical )) (PreH16 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH19 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH20 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH21 : ((old.(dly) ) <= UINT_MAX)) (PreH22 : (retval <= UINT_MAX)) (PreH23 : (ticks <= UINT_MAX)) (PreH24 : ((old.(dly) ) >= 0)) (PreH25 : (retval >= 0)) (PreH26 : (ticks >= 0)) (PreH27 : ((mbox_message_ptr (mailbox)) = 0)) (PreH28 : (environment = (Some (owned)))) (PreH29 : (external = (task_stack_call_external (owned)))) (PreH30 : (platform = (task_stack_call_platform (owned)))) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH33 : ((mbox_message_ptr (mailbox)) = 0)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (mbox_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (mbox_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current_2.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current_2.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current_2 resume_tid node )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current_2 ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 = (encode_pend_status ((node.(statPend) )))) ”
  &&  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current_2.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current_2.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current_2 resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_21 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current_2 )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (environment = (Some (owned_2)))) (PreH12 : (external = (task_stack_call_external (owned_2)))) (PreH13 : (platform = (task_stack_call_platform (owned_2)))) (PreH14 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH15 : (mbox_pend_sched_admitted environment critical )) (PreH16 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH17 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH18 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH19 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH20 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH21 : ((old.(dly) ) <= UINT_MAX)) (PreH22 : (retval <= UINT_MAX)) (PreH23 : (ticks <= UINT_MAX)) (PreH24 : ((old.(dly) ) >= 0)) (PreH25 : (retval >= 0)) (PreH26 : (ticks >= 0)) (PreH27 : ((mbox_message_ptr (mailbox)) = 0)) (PreH28 : (environment = (Some (owned)))) (PreH29 : (external = (task_stack_call_external (owned)))) (PreH30 : (platform = (task_stack_call_platform (owned)))) (PreH31 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH32 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH33 : ((mbox_message_ptr (mailbox)) = 0)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (mbox_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (mbox_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current_2.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current_2.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current_2 resume_tid node )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current_2 ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 <> (encode_pend_status ((node.(statPend) )))) ”
  &&  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current_2.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current_2.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current_2 resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH69 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH70 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 0) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 2) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH69 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH70 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 0) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 2) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 <> (encode_pend_status ((node.(statPend) )))) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_22 := OSMboxPend_partial_solve_wit_22_pure -> OSMboxPend_partial_solve_wit_22_aux.

Definition OSMboxPend_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH69 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH70 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (mailbox)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 0) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 2) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (mailbox: MboxFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (owned_2: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (environment = (Some (owned_2)))) (PreH7 : (external = (task_stack_call_external (owned_2)))) (PreH8 : (platform = (task_stack_call_platform (owned_2)))) (PreH9 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH10 : (mbox_pend_sched_admitted environment critical )) (PreH11 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) (PreH12 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH13 : (mbox_pend_wait_entry sg entry eid current tid old )) (PreH14 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH15 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH16 : ((old.(dly) ) <= UINT_MAX)) (PreH17 : (retval <= UINT_MAX)) (PreH18 : (ticks <= UINT_MAX)) (PreH19 : ((old.(dly) ) >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (ticks >= 0)) (PreH22 : ((mbox_message_ptr (mailbox)) = 0)) (PreH23 : (environment = (Some (owned)))) (PreH24 : (external = (task_stack_call_external (owned)))) (PreH25 : (platform = (task_stack_call_platform (owned)))) (PreH26 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH27 : (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH28 : ((mbox_message_ptr (mailbox)) = 0)) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (mbox_pend_api_prefix pe before eid )) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH32 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH33 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH36 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (UCOS2_state_inv sg before )) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH41 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH42 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH43 : (timeout_pre <= UINT_MAX)) (PreH44 : (0 <= UINT_MAX)) (PreH45 : (timeout_pre >= 0)) (PreH46 : (0 >= 0)) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH49 : (pe = (event_addr (sg) (eid)))) (PreH50 : (valid_event_id sg eid )) (PreH51 : (q_query_public_slot before eid observed )) (PreH52 : (UCOS2_state_inv sg before )) (PreH53 : (pevent_pre <> 0)) (PreH54 : (pevent_pre = pe)) (PreH55 : (timeout_pre = ticks)) (PreH56 : (perr_pre = pd)) (PreH57 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH58 : (sem_pend_profile sg )) (PreH59 : (mbox_accept_profile sg )) (PreH60 : (kernel_tcb_stack_field_layout sg )) (PreH61 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH62 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH63 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH64 : (pe <> 0)) (PreH65 : (event_object_layout_prop sg eid )) (PreH66 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH67 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH68 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH69 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH70 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 0) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 2) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (environment = (Some (owned_2))) ” 
  &&  “ (external = (task_stack_call_external (owned_2))) ” 
  &&  “ (platform = (task_stack_call_platform (owned_2))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ” 
  &&  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((mbox_message_ptr (mailbox)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (mbox_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 = (encode_pend_status ((node.(statPend) )))) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPend_partial_solve_wit_23 := OSMboxPend_partial_solve_wit_23_pure -> OSMboxPend_partial_solve_wit_23_aux.

Definition OSMboxPend_partial_solve_wit_24_pure := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  “ (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSMboxPend_partial_solve_wit_24_aux := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (mbox_pend_api_prefix pe before eid )) (PreH3 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  “ (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
.

Definition OSMboxPend_partial_solve_wit_24 := OSMboxPend_partial_solve_wit_24_pure -> OSMboxPend_partial_solve_wit_24_aux.

Definition OSMboxPend_partial_solve_wit_25_pure := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> code)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPend_partial_solve_wit_25_aux := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (mbox_pend_api_prefix pe before eid )) (PreH4 : (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (q_pend_resume_result sg eid resume_entry pmsg code checkpoint ) ” 
  &&  “ (mbox_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ” 
  &&  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (mbox_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((pd) # UChar  |-> code)
.

Definition OSMboxPend_partial_solve_wit_25 := OSMboxPend_partial_solve_wit_25_pure -> OSMboxPend_partial_solve_wit_25_aux.

Definition OSMboxPend_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
).

Definition OSMboxPend_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMboxPend_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (q_query_public_slot before eid observed ) ”
.

Definition OSMboxPend_which_implies_wit_1_split_goal_3 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSMboxPend_which_implies_wit_1_split_goal_4 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxPend_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
.

Definition OSMboxPend_which_implies_wit_2 := 
(
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
) \/
(
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
).

Definition OSMboxPend_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
.

Definition OSMboxPend_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_api_prefix pe before eid ) ”
  &&  (mbox_pend_save_input (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  “ (mbox_pend_api_prefix pe before eid ) ”
  &&  (mbox_pend_save_input (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
).

Definition OSMboxPend_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  “ (mbox_pend_api_prefix pe before eid ) ”
.

Definition OSMboxPend_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (mbox_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 1)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  (mbox_pend_save_input (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
.

Definition OSMboxPend_which_implies_wit_4 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_accept_profile sg )) (PreH2 : (valid_event_id sg eid )) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH4 : (pevent = (event_addr (sg) (eid)))) ,
  (mbox_pend_save_output (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask cpu_sr before )
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (mailbox: MboxFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed current mailbox )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_accept_profile sg )) (PreH2 : (valid_event_id sg eid )) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH4 : (pevent = (event_addr (sg) (eid)))) ,
  (mbox_pend_save_output (MboxPendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask cpu_sr before )
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (mailbox: MboxFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_pend_message_frame external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed current mailbox )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
).

Definition OSMboxPend_which_implies_wit_5 := 
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (current: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (pmsg: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pmsg = (mbox_message_ptr (mailbox)))) (PreH2 : (pmsg <> 0)) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) ,
  (mbox_pend_message_frame external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed current mailbox )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks pmsg checkpoint ) ”
  &&  (mbox_pend_restore_input None external platform environment critical saved_local sg entered mask cpu_sr entry checkpoint )
) \/
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (current: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (pmsg: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pmsg = (mbox_message_ptr (mailbox)))) (PreH2 : (pmsg <> 0)) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) ,
  (mbox_pend_message_frame external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed current mailbox )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks pmsg checkpoint ) ”
  &&  (mbox_pend_restore_input None external platform environment critical saved_local sg entered mask cpu_sr entry checkpoint )
).

Definition OSMboxPend_which_implies_wit_6 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (pmsg: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pmsg = (mbox_message_ptr (mailbox)))) (PreH2 : (pmsg = 0)) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_message_frame external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed current_2 mailbox )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState)  (owned: TaskStackCallEnvironment) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pmsg = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old ) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (mailbox: MboxFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (pmsg: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pmsg = (mbox_message_ptr (mailbox)))) (PreH2 : (pmsg = 0)) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_message_frame external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed current_2 mailbox )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (mailbox)))
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState)  (owned: TaskStackCallEnvironment) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pmsg = 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old ) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
).

Definition OSMboxPend_which_implies_wit_7 := 
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  “ (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old ) ” 
  &&  “ (mbox_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
) \/
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (ticks <= UINT_MAX)) (PreH2 : (ticks >= 0)) (PreH3 : (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  “ (mbox_pend_wait_entry sg entry eid current tid old ) ”
  &&  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
).

Definition OSMboxPend_which_implies_wit_7_split_goal_1 := 
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (ticks <= UINT_MAX)) (PreH2 : (ticks >= 0)) (PreH3 : (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  “ (mbox_pend_wait_entry sg entry eid current tid old ) ”
.

Definition OSMboxPend_which_implies_wit_7_split_goal_spatial := 
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (ticks <= UINT_MAX)) (PreH2 : (ticks >= 0)) (PreH3 : (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 2))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  (mbox_pend_wait_call_pre sg entry eid current tid old ticks )
.

Definition OSMboxPend_which_implies_wit_8 := 
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH2 : (kernel_tcb_stack_field_layout sg )) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  (mbox_pend_wait_call_post sg entry eid current tid old ticks )
|--
  EX (waiting: UCOS2_Verify_State) ,
  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ”
  &&  (mbox_pend_restore_input (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask cpu_sr entry waiting )
) \/
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (mbox_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH2 : (kernel_tcb_stack_field_layout sg )) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  (mbox_pend_wait_call_post sg entry eid current tid old ticks )
|--
  EX (waiting: UCOS2_Verify_State) ,
  “ (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting ) ”
  &&  (mbox_pend_restore_input (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask cpu_sr entry waiting )
).

Definition OSMboxPend_which_implies_wit_9 := 
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (waiting: UCOS2_Verify_State) (entered: OsSchedCallContext) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) ,
  (mbox_pend_restore_output (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask waiting )
|--
  EX (released: OsSchedCallContext)  (unmasked: UCOS2_Verify_State)  (owned: TaskStackCallEnvironment) ,
  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ”
  &&  (mbox_sched_continuation_phase_sched_input (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
) \/
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (waiting: UCOS2_Verify_State) (entered: OsSchedCallContext) (PreH1 : (mbox_pend_first_wait_checkpoint external environment critical sg context before entered eid ticks waiting )) ,
  (mbox_pend_restore_output (Some ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg entered mask waiting )
|--
  EX (released: OsSchedCallContext)  (unmasked: UCOS2_Verify_State)  (owned: TaskStackCallEnvironment) ,
  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked ) ” 
  &&  “ (mbox_pend_sched_admitted environment critical ) ”
  &&  (mbox_sched_continuation_phase_sched_input (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
).

Definition OSMboxPend_which_implies_wit_10 := 
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (unmasked: UCOS2_Verify_State) (released: OsSchedCallContext) (owned: TaskStackCallEnvironment) (PreH1 : (environment = (Some (owned)))) (PreH2 : (external = (task_stack_call_external (owned)))) (PreH3 : (platform = (task_stack_call_platform (owned)))) (PreH4 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH5 : (mbox_pend_sched_admitted environment critical )) ,
  (mbox_sched_continuation_phase_sched_output (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
|--
  EX (scheduled: OsSchedCallContext)  (selected: UCOS2_Verify_State) ,
  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ”
  &&  (mbox_pend_save_input (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg scheduled mask selected )
) \/
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (unmasked: UCOS2_Verify_State) (released: OsSchedCallContext) (owned: TaskStackCallEnvironment) (PreH1 : (environment = (Some (owned)))) (PreH2 : (external = (task_stack_call_external (owned)))) (PreH3 : (platform = (task_stack_call_platform (owned)))) (PreH4 : (mbox_pend_scheduling_checkpoint external environment critical sg context before eid ticks released unmasked )) (PreH5 : (mbox_pend_sched_admitted environment critical )) ,
  (mbox_sched_continuation_phase_sched_output (MboxPendWaitPhase (context) (mask) (eid)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
|--
  EX (scheduled: OsSchedCallContext)  (selected: UCOS2_Verify_State) ,
  “ (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ”
  &&  (mbox_pend_save_input (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg scheduled mask selected )
).

Definition OSMboxPend_which_implies_wit_11 := 
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_save_output (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg scheduled mask cpu_sr selected )
|--
  EX (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
) \/
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mbox_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_save_output (MboxPendResumePhase ((MboxPendWaitPhase (context) (mask) (eid)))) external platform environment critical saved_local sg scheduled mask cpu_sr selected )
|--
  EX (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (mbox_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
).

Definition OSMboxPend_which_implies_wit_12 := 
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
|--
  EX (cleaning: UCOS2_Verify_State)  (cleaned_node: TaskAbstractState) ,
  “ (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
) \/
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
|--
  EX (cleaning: UCOS2_Verify_State)  (cleaned_node: TaskAbstractState) ,
  “ (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
).

Definition OSMboxPend_which_implies_wit_13 := 
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((encode_pend_status ((node.(statPend) ))) <> 0)) (PreH3 : ((encode_pend_status ((node.(statPend) ))) <> 2)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
|--
  EX (current: OSEventAbstractState) ,
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
) \/
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((encode_pend_status ((node.(statPend) ))) <> 0)) (PreH3 : ((encode_pend_status ((node.(statPend) ))) <> 2)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
|--
  EX (current: OSEventAbstractState) ,
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
).

Definition OSMboxPend_which_implies_wit_14 := 
(
forall (eid: Z) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (code: Z) (node: TaskAbstractState) (resume_tid: Z) (cleaning: UCOS2_Verify_State) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (pmsg: Z) (cpu_sr: Z) (perr: Z) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((perr) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  EX (checkpoint: UCOS2_Verify_State) ,
  “ (q_pend_resume_result sg eid resume_entry pmsg code checkpoint ) ”
  &&  (mbox_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((perr) # UChar  |-> code)
) \/
(
forall (eid: Z) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (code: Z) (node: TaskAbstractState) (resume_tid: Z) (cleaning: UCOS2_Verify_State) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (pmsg: Z) (cpu_sr: Z) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (mbox_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  EX (checkpoint: UCOS2_Verify_State) ,
  “ (q_pend_resume_result sg eid resume_entry pmsg code checkpoint ) ”
  &&  (mbox_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxPend_safety_wit_1 : OSMboxPend_safety_wit_1.
Axiom proof_of_OSMboxPend_safety_wit_2 : OSMboxPend_safety_wit_2.
Axiom proof_of_OSMboxPend_safety_wit_3 : OSMboxPend_safety_wit_3.
Axiom proof_of_OSMboxPend_safety_wit_4 : OSMboxPend_safety_wit_4.
Axiom proof_of_OSMboxPend_safety_wit_5 : OSMboxPend_safety_wit_5.
Axiom proof_of_OSMboxPend_safety_wit_6 : OSMboxPend_safety_wit_6.
Axiom proof_of_OSMboxPend_safety_wit_7 : OSMboxPend_safety_wit_7.
Axiom proof_of_OSMboxPend_safety_wit_8 : OSMboxPend_safety_wit_8.
Axiom proof_of_OSMboxPend_safety_wit_9 : OSMboxPend_safety_wit_9.
Axiom proof_of_OSMboxPend_safety_wit_10 : OSMboxPend_safety_wit_10.
Axiom proof_of_OSMboxPend_safety_wit_11 : OSMboxPend_safety_wit_11.
Axiom proof_of_OSMboxPend_safety_wit_12 : OSMboxPend_safety_wit_12.
Axiom proof_of_OSMboxPend_safety_wit_13 : OSMboxPend_safety_wit_13.
Axiom proof_of_OSMboxPend_safety_wit_14 : OSMboxPend_safety_wit_14.
Axiom proof_of_OSMboxPend_safety_wit_15 : OSMboxPend_safety_wit_15.
Axiom proof_of_OSMboxPend_safety_wit_16 : OSMboxPend_safety_wit_16.
Axiom proof_of_OSMboxPend_safety_wit_17 : OSMboxPend_safety_wit_17.
Axiom proof_of_OSMboxPend_safety_wit_18 : OSMboxPend_safety_wit_18.
Axiom proof_of_OSMboxPend_safety_wit_19 : OSMboxPend_safety_wit_19.
Axiom proof_of_OSMboxPend_safety_wit_20 : OSMboxPend_safety_wit_20.
Axiom proof_of_OSMboxPend_entail_wit_1 : OSMboxPend_entail_wit_1.
Axiom proof_of_OSMboxPend_entail_wit_2 : OSMboxPend_entail_wit_2.
Axiom proof_of_OSMboxPend_entail_wit_3 : OSMboxPend_entail_wit_3.
Axiom proof_of_OSMboxPend_entail_wit_4 : OSMboxPend_entail_wit_4.
Axiom proof_of_OSMboxPend_entail_wit_5_1 : OSMboxPend_entail_wit_5_1.
Axiom proof_of_OSMboxPend_entail_wit_5_2 : OSMboxPend_entail_wit_5_2.
Axiom proof_of_OSMboxPend_entail_wit_5_3 : OSMboxPend_entail_wit_5_3.
Axiom proof_of_OSMboxPend_entail_wit_5_4 : OSMboxPend_entail_wit_5_4.
Axiom proof_of_OSMboxPend_return_wit_1 : OSMboxPend_return_wit_1.
Axiom proof_of_OSMboxPend_return_wit_2 : OSMboxPend_return_wit_2.
Axiom proof_of_OSMboxPend_return_wit_3 : OSMboxPend_return_wit_3.
Axiom proof_of_OSMboxPend_return_wit_4 : OSMboxPend_return_wit_4.
Axiom proof_of_OSMboxPend_return_wit_5 : OSMboxPend_return_wit_5.
Axiom proof_of_OSMboxPend_return_wit_6 : OSMboxPend_return_wit_6.
Axiom proof_of_OSMboxPend_partial_solve_wit_1_pure : OSMboxPend_partial_solve_wit_1_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_1 : OSMboxPend_partial_solve_wit_1.
Axiom proof_of_OSMboxPend_partial_solve_wit_2_pure : OSMboxPend_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_2 : OSMboxPend_partial_solve_wit_2.
Axiom proof_of_OSMboxPend_partial_solve_wit_3_pure : OSMboxPend_partial_solve_wit_3_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_3 : OSMboxPend_partial_solve_wit_3.
Axiom proof_of_OSMboxPend_partial_solve_wit_4 : OSMboxPend_partial_solve_wit_4.
Axiom proof_of_OSMboxPend_partial_solve_wit_5_pure : OSMboxPend_partial_solve_wit_5_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_5 : OSMboxPend_partial_solve_wit_5.
Axiom proof_of_OSMboxPend_partial_solve_wit_6_pure : OSMboxPend_partial_solve_wit_6_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_6 : OSMboxPend_partial_solve_wit_6.
Axiom proof_of_OSMboxPend_partial_solve_wit_7_pure : OSMboxPend_partial_solve_wit_7_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_7 : OSMboxPend_partial_solve_wit_7.
Axiom proof_of_OSMboxPend_partial_solve_wit_8_pure : OSMboxPend_partial_solve_wit_8_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_8 : OSMboxPend_partial_solve_wit_8.
Axiom proof_of_OSMboxPend_partial_solve_wit_9_pure : OSMboxPend_partial_solve_wit_9_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_9 : OSMboxPend_partial_solve_wit_9.
Axiom proof_of_OSMboxPend_partial_solve_wit_10_pure : OSMboxPend_partial_solve_wit_10_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_10 : OSMboxPend_partial_solve_wit_10.
Axiom proof_of_OSMboxPend_partial_solve_wit_11_pure : OSMboxPend_partial_solve_wit_11_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_11 : OSMboxPend_partial_solve_wit_11.
Axiom proof_of_OSMboxPend_partial_solve_wit_12_pure : OSMboxPend_partial_solve_wit_12_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_12 : OSMboxPend_partial_solve_wit_12.
Axiom proof_of_OSMboxPend_partial_solve_wit_13_pure : OSMboxPend_partial_solve_wit_13_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_13 : OSMboxPend_partial_solve_wit_13.
Axiom proof_of_OSMboxPend_partial_solve_wit_14_pure : OSMboxPend_partial_solve_wit_14_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_14 : OSMboxPend_partial_solve_wit_14.
Axiom proof_of_OSMboxPend_partial_solve_wit_15_pure : OSMboxPend_partial_solve_wit_15_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_15 : OSMboxPend_partial_solve_wit_15.
Axiom proof_of_OSMboxPend_partial_solve_wit_16 : OSMboxPend_partial_solve_wit_16.
Axiom proof_of_OSMboxPend_partial_solve_wit_17_pure : OSMboxPend_partial_solve_wit_17_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_17 : OSMboxPend_partial_solve_wit_17.
Axiom proof_of_OSMboxPend_partial_solve_wit_18_pure : OSMboxPend_partial_solve_wit_18_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_18 : OSMboxPend_partial_solve_wit_18.
Axiom proof_of_OSMboxPend_partial_solve_wit_19_pure : OSMboxPend_partial_solve_wit_19_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_19 : OSMboxPend_partial_solve_wit_19.
Axiom proof_of_OSMboxPend_partial_solve_wit_20 : OSMboxPend_partial_solve_wit_20.
Axiom proof_of_OSMboxPend_partial_solve_wit_21 : OSMboxPend_partial_solve_wit_21.
Axiom proof_of_OSMboxPend_partial_solve_wit_22_pure : OSMboxPend_partial_solve_wit_22_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_22 : OSMboxPend_partial_solve_wit_22.
Axiom proof_of_OSMboxPend_partial_solve_wit_23_pure : OSMboxPend_partial_solve_wit_23_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_23 : OSMboxPend_partial_solve_wit_23.
Axiom proof_of_OSMboxPend_partial_solve_wit_24_pure : OSMboxPend_partial_solve_wit_24_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_24 : OSMboxPend_partial_solve_wit_24.
Axiom proof_of_OSMboxPend_partial_solve_wit_25_pure : OSMboxPend_partial_solve_wit_25_pure.
Axiom proof_of_OSMboxPend_partial_solve_wit_25 : OSMboxPend_partial_solve_wit_25.
Axiom proof_of_OSMboxPend_which_implies_wit_1 : OSMboxPend_which_implies_wit_1.
Axiom proof_of_OSMboxPend_which_implies_wit_2 : OSMboxPend_which_implies_wit_2.
Axiom proof_of_OSMboxPend_which_implies_wit_3 : OSMboxPend_which_implies_wit_3.
Axiom proof_of_OSMboxPend_which_implies_wit_4 : OSMboxPend_which_implies_wit_4.
Axiom proof_of_OSMboxPend_which_implies_wit_5 : OSMboxPend_which_implies_wit_5.
Axiom proof_of_OSMboxPend_which_implies_wit_6 : OSMboxPend_which_implies_wit_6.
Axiom proof_of_OSMboxPend_which_implies_wit_7 : OSMboxPend_which_implies_wit_7.
Axiom proof_of_OSMboxPend_which_implies_wit_8 : OSMboxPend_which_implies_wit_8.
Axiom proof_of_OSMboxPend_which_implies_wit_9 : OSMboxPend_which_implies_wit_9.
Axiom proof_of_OSMboxPend_which_implies_wit_10 : OSMboxPend_which_implies_wit_10.
Axiom proof_of_OSMboxPend_which_implies_wit_11 : OSMboxPend_which_implies_wit_11.
Axiom proof_of_OSMboxPend_which_implies_wit_12 : OSMboxPend_which_implies_wit_12.
Axiom proof_of_OSMboxPend_which_implies_wit_13 : OSMboxPend_which_implies_wit_13.
Axiom proof_of_OSMboxPend_which_implies_wit_14 : OSMboxPend_which_implies_wit_14.

End VC_Correct.
