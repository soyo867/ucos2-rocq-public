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
Require Import Ucos2Verify.VC.code.queue.spec.q_pend_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQPend -----*)

Definition OSQPend_safety_wit_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (timeout_pre = ticks)) (PreH3 : (perr_pre = pd)) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (sem_pend_profile sg )) (PreH6 : (q_accept_profile sg )) (PreH7 : (kernel_tcb_stack_field_layout sg )) (PreH8 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH9 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH10 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH11 : (pe = 0)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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

Definition OSQPend_safety_wit_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (timeout_pre = ticks)) (PreH3 : (perr_pre = pd)) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (sem_pend_profile sg )) (PreH6 : (q_accept_profile sg )) (PreH7 : (kernel_tcb_stack_field_layout sg )) (PreH8 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH9 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH10 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH11 : (pe <> 0)) (PreH12 : (event_object_layout_prop sg eid )) (PreH13 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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

Definition OSQPend_safety_wit_3 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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

Definition OSQPend_safety_wit_4 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe <> 0)) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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

Definition OSQPend_safety_wit_5 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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

Definition OSQPend_safety_wit_6 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (q_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_7 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_8 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (q_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_9 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (q_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_output (QueuePendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_10 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_4)))) (PreH5 : ((queue_entries (q_4)) <= 65535)) (PreH6 : (0 < (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : ((queue_entries (q_2)) > 0)) (PreH9 : (0 <= (queue_entries (q_2)))) (PreH10 : ((queue_entries (q_2)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_11 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_4)))) (PreH5 : ((queue_entries (q_4)) <= 65535)) (PreH6 : (0 < (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : ((queue_entries (q_2)) > 0)) (PreH9 : (0 <= (queue_entries (q_2)))) (PreH10 : ((queue_entries (q_2)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_12 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH2 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (q_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask waiting )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_13 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH4 : (q_pend_sched_admitted environment critical )) (PreH5 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH6 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH7 : (q_pend_wait_entry sg entry eid current tid old )) (PreH8 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH9 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH10 : ((old.(dly) ) <= UINT_MAX)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (ticks <= UINT_MAX)) (PreH13 : ((old.(dly) ) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (ticks >= 0)) (PreH16 : (environment = (Some (owned)))) (PreH17 : (external = (task_stack_call_external (owned)))) (PreH18 : (platform = (task_stack_call_platform (owned)))) (PreH19 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH20 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH21 : ((queue_entries (q_2)) <= 0)) (PreH22 : (0 <= (queue_entries (q_2)))) (PreH23 : ((queue_entries (q_2)) <= 65535)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (q_pend_api_prefix pe before eid )) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH27 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH36 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH38 : (timeout_pre <= UINT_MAX)) (PreH39 : (0 <= UINT_MAX)) (PreH40 : (timeout_pre >= 0)) (PreH41 : (0 >= 0)) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (pe = (event_addr (sg) (eid)))) (PreH45 : (valid_event_id sg eid )) (PreH46 : (q_query_public_slot before eid observed )) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : (pevent_pre <> 0)) (PreH49 : (pevent_pre = pe)) (PreH50 : (timeout_pre = ticks)) (PreH51 : (perr_pre = pd)) (PreH52 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH53 : (sem_pend_profile sg )) (PreH54 : (q_accept_profile sg )) (PreH55 : (kernel_tcb_stack_field_layout sg )) (PreH56 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH57 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH58 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH59 : (pe <> 0)) (PreH60 : (event_object_layout_prop sg eid )) (PreH61 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH62 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_output (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg scheduled mask retval_2 selected )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_14 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q_2)) <= 0)) (PreH25 : (0 <= (queue_entries (q_2)))) (PreH26 : ((queue_entries (q_2)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH67 : (2 = (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_15 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : ((node.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH9 : (interrupt_saved_value mask retval_2 )) (PreH10 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH11 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH14 : (q_pend_sched_admitted environment critical )) (PreH15 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : (q_pend_wait_entry sg entry eid current tid old )) (PreH18 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH19 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH20 : ((old.(dly) ) <= UINT_MAX)) (PreH21 : (retval <= UINT_MAX)) (PreH22 : (ticks <= UINT_MAX)) (PreH23 : ((old.(dly) ) >= 0)) (PreH24 : (retval >= 0)) (PreH25 : (ticks >= 0)) (PreH26 : (environment = (Some (owned)))) (PreH27 : (external = (task_stack_call_external (owned)))) (PreH28 : (platform = (task_stack_call_platform (owned)))) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH31 : ((queue_entries (q_2)) <= 0)) (PreH32 : (0 <= (queue_entries (q_2)))) (PreH33 : ((queue_entries (q_2)) <= 65535)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (q_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (q_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_16 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : ((node.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH9 : (interrupt_saved_value mask retval_2 )) (PreH10 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH11 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH14 : (q_pend_sched_admitted environment critical )) (PreH15 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : (q_pend_wait_entry sg entry eid current tid old )) (PreH18 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH19 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH20 : ((old.(dly) ) <= UINT_MAX)) (PreH21 : (retval <= UINT_MAX)) (PreH22 : (ticks <= UINT_MAX)) (PreH23 : ((old.(dly) ) >= 0)) (PreH24 : (retval >= 0)) (PreH25 : (ticks >= 0)) (PreH26 : (environment = (Some (owned)))) (PreH27 : (external = (task_stack_call_external (owned)))) (PreH28 : (platform = (task_stack_call_platform (owned)))) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH31 : ((queue_entries (q_2)) <= 0)) (PreH32 : (0 <= (queue_entries (q_2)))) (PreH33 : ((queue_entries (q_2)) <= 65535)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (q_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (q_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH75 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_safety_wit_17 := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pq: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
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

Definition OSQPend_safety_wit_18 := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pq: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
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

Definition OSQPend_safety_wit_19 := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pq: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> code)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPend_entail_wit_1 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH2 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_query_public_slot before eid observed )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (timeout_pre = ticks)) (PreH10 : (perr_pre = pd)) (PreH11 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH12 : (sem_pend_profile sg )) (PreH13 : (q_accept_profile sg )) (PreH14 : (kernel_tcb_stack_field_layout sg )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH17 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH18 : (pe <> 0)) (PreH19 : (event_object_layout_prop sg eid )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
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
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (timeout_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (timeout_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_query_public_slot before eid observed )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (timeout_pre = ticks)) (PreH14 : (perr_pre = pd)) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (sem_pend_profile sg )) (PreH17 : (q_accept_profile sg )) (PreH18 : (kernel_tcb_stack_field_layout sg )) (PreH19 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH20 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH21 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH22 : (pe <> 0)) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ”
  &&  emp
).

Definition OSQPend_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (timeout_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (timeout_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_query_public_slot before eid observed )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (timeout_pre = ticks)) (PreH14 : (perr_pre = pd)) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (sem_pend_profile sg )) (PreH17 : (q_accept_profile sg )) (PreH18 : (kernel_tcb_stack_field_layout sg )) (PreH19 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH20 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH21 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH22 : (pe <> 0)) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)
.

Definition OSQPend_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (timeout_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (timeout_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_query_public_slot before eid observed )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (timeout_pre = ticks)) (PreH14 : (perr_pre = pd)) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (sem_pend_profile sg )) (PreH17 : (q_accept_profile sg )) (PreH18 : (kernel_tcb_stack_field_layout sg )) (PreH19 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH20 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH21 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH22 : (pe <> 0)) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))
.

Definition OSQPend_entail_wit_2 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (q_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
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
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (q_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ”
  &&  emp
).

Definition OSQPend_entail_wit_2_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (q_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (((before.(IntrState) ).(intNesting) ) <= 255)
.

Definition OSQPend_entail_wit_2_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (timeout_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (timeout_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (timeout_pre = ticks)) (PreH20 : (perr_pre = pd)) (PreH21 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH22 : (sem_pend_profile sg )) (PreH23 : (q_accept_profile sg )) (PreH24 : (kernel_tcb_stack_field_layout sg )) (PreH25 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH27 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH28 : (pe <> 0)) (PreH29 : (event_object_layout_prop sg eid )) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= ((before.(IntrState) ).(intNesting) ))
.

Definition OSQPend_entail_wit_3 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
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
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ”
  &&  emp
).

Definition OSQPend_entail_wit_3_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (((before.(IntrState) ).(lockNesting) ) <= 255)
.

Definition OSQPend_entail_wit_3_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= ((before.(IntrState) ).(lockNesting) ))
.

Definition OSQPend_entail_wit_4 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (environment = (Some (owned)))) (PreH2 : (external = (task_stack_call_external (owned)))) (PreH3 : (platform = (task_stack_call_platform (owned)))) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH6 : ((queue_entries (q_2)) <= 0)) (PreH7 : (0 <= (queue_entries (q_2)))) (PreH8 : ((queue_entries (q_2)) <= 65535)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (q_pend_api_prefix pe before eid )) (PreH11 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH12 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH14 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH15 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH21 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH23 : (timeout_pre <= UINT_MAX)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (timeout_pre >= 0)) (PreH26 : (0 >= 0)) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (valid_event_id sg eid )) (PreH31 : (q_query_public_slot before eid observed )) (PreH32 : (UCOS2_state_inv sg before )) (PreH33 : (pevent_pre <> 0)) (PreH34 : (pevent_pre = pe)) (PreH35 : (timeout_pre = ticks)) (PreH36 : (perr_pre = pd)) (PreH37 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH38 : (sem_pend_profile sg )) (PreH39 : (q_accept_profile sg )) (PreH40 : (kernel_tcb_stack_field_layout sg )) (PreH41 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH42 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH43 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH44 : (pe <> 0)) (PreH45 : (event_object_layout_prop sg eid )) (PreH46 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH47 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
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
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((old.(dly) ) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (ticks <= UINT_MAX)) (PreH4 : ((old.(dly) ) >= 0)) (PreH5 : (retval >= 0)) (PreH6 : (ticks >= 0)) (PreH7 : (environment = (Some (owned)))) (PreH8 : (external = (task_stack_call_external (owned)))) (PreH9 : (platform = (task_stack_call_platform (owned)))) (PreH10 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH11 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH12 : ((queue_entries (q_2)) <= 0)) (PreH13 : (0 <= (queue_entries (q_2)))) (PreH14 : ((queue_entries (q_2)) <= 65535)) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (q_pend_api_prefix pe before eid )) (PreH17 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH19 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH20 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH22 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH27 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH28 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH29 : (timeout_pre <= UINT_MAX)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (timeout_pre >= 0)) (PreH32 : (0 >= 0)) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH35 : (pe = (event_addr (sg) (eid)))) (PreH36 : (valid_event_id sg eid )) (PreH37 : (q_query_public_slot before eid observed )) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : (pevent_pre <> 0)) (PreH40 : (pevent_pre = pe)) (PreH41 : (timeout_pre = ticks)) (PreH42 : (perr_pre = pd)) (PreH43 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH44 : (sem_pend_profile sg )) (PreH45 : (q_accept_profile sg )) (PreH46 : (kernel_tcb_stack_field_layout sg )) (PreH47 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH48 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH49 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH50 : (pe <> 0)) (PreH51 : (event_object_layout_prop sg eid )) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ”
  &&  emp
).

Definition OSQPend_entail_wit_4_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((old.(dly) ) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (ticks <= UINT_MAX)) (PreH4 : ((old.(dly) ) >= 0)) (PreH5 : (retval >= 0)) (PreH6 : (ticks >= 0)) (PreH7 : (environment = (Some (owned)))) (PreH8 : (external = (task_stack_call_external (owned)))) (PreH9 : (platform = (task_stack_call_platform (owned)))) (PreH10 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH11 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH12 : ((queue_entries (q_2)) <= 0)) (PreH13 : (0 <= (queue_entries (q_2)))) (PreH14 : ((queue_entries (q_2)) <= 65535)) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (q_pend_api_prefix pe before eid )) (PreH17 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH19 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH20 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH22 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH27 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH28 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH29 : (timeout_pre <= UINT_MAX)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (timeout_pre >= 0)) (PreH32 : (0 >= 0)) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH35 : (pe = (event_addr (sg) (eid)))) (PreH36 : (valid_event_id sg eid )) (PreH37 : (q_query_public_slot before eid observed )) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : (pevent_pre <> 0)) (PreH40 : (pevent_pre = pe)) (PreH41 : (timeout_pre = ticks)) (PreH42 : (perr_pre = pd)) (PreH43 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH44 : (sem_pend_profile sg )) (PreH45 : (q_accept_profile sg )) (PreH46 : (kernel_tcb_stack_field_layout sg )) (PreH47 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH48 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH49 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH50 : (pe <> 0)) (PreH51 : (event_object_layout_prop sg eid )) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((encode_task_status ((old.(stat) ))) <= 255)
.

Definition OSQPend_entail_wit_4_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : ((old.(dly) ) <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (ticks <= UINT_MAX)) (PreH4 : ((old.(dly) ) >= 0)) (PreH5 : (retval >= 0)) (PreH6 : (ticks >= 0)) (PreH7 : (environment = (Some (owned)))) (PreH8 : (external = (task_stack_call_external (owned)))) (PreH9 : (platform = (task_stack_call_platform (owned)))) (PreH10 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH11 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH12 : ((queue_entries (q_2)) <= 0)) (PreH13 : (0 <= (queue_entries (q_2)))) (PreH14 : ((queue_entries (q_2)) <= 65535)) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (q_pend_api_prefix pe before eid )) (PreH17 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH19 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH20 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH21 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH22 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH27 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH28 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH29 : (timeout_pre <= UINT_MAX)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (timeout_pre >= 0)) (PreH32 : (0 >= 0)) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH35 : (pe = (event_addr (sg) (eid)))) (PreH36 : (valid_event_id sg eid )) (PreH37 : (q_query_public_slot before eid observed )) (PreH38 : (UCOS2_state_inv sg before )) (PreH39 : (pevent_pre <> 0)) (PreH40 : (pevent_pre = pe)) (PreH41 : (timeout_pre = ticks)) (PreH42 : (perr_pre = pd)) (PreH43 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH44 : (sem_pend_profile sg )) (PreH45 : (q_accept_profile sg )) (PreH46 : (kernel_tcb_stack_field_layout sg )) (PreH47 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH48 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH49 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH50 : (pe <> 0)) (PreH51 : (event_object_layout_prop sg eid )) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (encode_task_status ((old.(stat) ))))
.

Definition OSQPend_entail_wit_5_1 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval_2 <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval_2 >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q)) <= 0)) (PreH25 : (0 <= (queue_entries (q)))) (PreH26 : ((queue_entries (q)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 = (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 resume_entry_2 )
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
  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid (encode_msg ((node.(msg) ))) code cleaning resume_tid node_2 ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node_2.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node_2.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node_2.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node_2.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node_2 )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval_2 <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval_2 >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q)) <= 0)) (PreH25 : (0 <= (queue_entries (q)))) (PreH26 : ((queue_entries (q)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 = (encode_pend_status ((node.(statPend) ))))) ,
  TT && emp 
|--
  “ (q_pend_cleanup_observation sg resume_entry_2 eid (encode_msg ((node.(msg) ))) 0 resume_entry_2 resume_tid_2 node ) ”
  &&  emp
).

Definition OSQPend_entail_wit_5_1_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval_2 <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval_2 >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q)) <= 0)) (PreH25 : (0 <= (queue_entries (q)))) (PreH26 : ((queue_entries (q)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 = (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_cleanup_observation sg resume_entry_2 eid (encode_msg ((node.(msg) ))) 0 resume_entry_2 resume_tid_2 node )
.

Definition OSQPend_entail_wit_5_2 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval_2 <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval_2 >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q)) <= 0)) (PreH25 : (0 <= (queue_entries (q)))) (PreH26 : ((queue_entries (q)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH67 : (2 = (encode_pend_status ((node_2.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 resume_entry_2 )
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
  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid 0 code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval_2 <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval_2 >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q)) <= 0)) (PreH25 : (0 <= (queue_entries (q)))) (PreH26 : ((queue_entries (q)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH67 : (2 = (encode_pend_status ((node_2.(statPend) ))))) ,
  TT && emp 
|--
  “ (q_pend_cleanup_observation sg resume_entry_2 eid 0 14 resume_entry_2 resume_tid_2 node_2 ) ”
  &&  emp
).

Definition OSQPend_entail_wit_5_2_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval_2 <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval_2 >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q)) <= 0)) (PreH25 : (0 <= (queue_entries (q)))) (PreH26 : ((queue_entries (q)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH67 : (2 = (encode_pend_status ((node_2.(statPend) ))))) ,
  (q_pend_cleanup_observation sg resume_entry_2 eid 0 14 resume_entry_2 resume_tid_2 node_2 )
.

Definition OSQPend_entail_wit_5_3 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning_2: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry_2 eid 0 10 cleaning_2 resume_tid_2 cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : ((node_2.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry_2 eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH9 : (interrupt_saved_value mask retval )) (PreH10 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH11 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH14 : (q_pend_sched_admitted environment critical )) (PreH15 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH17 : (q_pend_wait_entry sg entry eid current tid old )) (PreH18 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH19 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH20 : ((old.(dly) ) <= UINT_MAX)) (PreH21 : (retval_2 <= UINT_MAX)) (PreH22 : (ticks <= UINT_MAX)) (PreH23 : ((old.(dly) ) >= 0)) (PreH24 : (retval_2 >= 0)) (PreH25 : (ticks >= 0)) (PreH26 : (environment = (Some (owned)))) (PreH27 : (external = (task_stack_call_external (owned)))) (PreH28 : (platform = (task_stack_call_platform (owned)))) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH31 : ((queue_entries (q)) <= 0)) (PreH32 : (0 <= (queue_entries (q)))) (PreH33 : ((queue_entries (q)) <= 65535)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (q_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (q_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH75 : (1 = (encode_pend_status ((node_2.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 cleaning_2 )
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
  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid 0 code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
.

Definition OSQPend_entail_wit_5_4 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval_2: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval: Z) (resume_tid_2: Z) (node_2: TaskAbstractState) (resumed_2: OsSchedCallContext) (resume_entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cleaning_2: UCOS2_Verify_State) (cleaned_node: TaskAbstractState) (PreH1 : (q_pend_cleanup_observation sg resume_entry_2 eid 0 10 cleaning_2 resume_tid_2 cleaned_node )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH4 : ((node_2.(statPend) ) = PendTimeout)) (PreH5 : (mutex_query_lookup resume_entry_2 eid current_2 )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH8 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed_2 resume_entry_2 )) (PreH9 : (interrupt_saved_value mask retval )) (PreH10 : (sem_pend_resume_entry sg resume_entry_2 eid resume_tid_2 node_2 )) (PreH11 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH14 : (q_pend_sched_admitted environment critical )) (PreH15 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH17 : (q_pend_wait_entry sg entry eid current tid old )) (PreH18 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH19 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH20 : ((old.(dly) ) <= UINT_MAX)) (PreH21 : (retval_2 <= UINT_MAX)) (PreH22 : (ticks <= UINT_MAX)) (PreH23 : ((old.(dly) ) >= 0)) (PreH24 : (retval_2 >= 0)) (PreH25 : (ticks >= 0)) (PreH26 : (environment = (Some (owned)))) (PreH27 : (external = (task_stack_call_external (owned)))) (PreH28 : (platform = (task_stack_call_platform (owned)))) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (q_pend_empty_snapshot external environment critical sg context entered mask retval_2 pe before entry eid observed current tid old )) (PreH31 : ((queue_entries (q)) <= 0)) (PreH32 : (0 <= (queue_entries (q)))) (PreH33 : ((queue_entries (q)) <= 65535)) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH35 : (q_pend_api_prefix pe before eid )) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH37 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH38 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH40 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH41 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH42 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (UCOS2_state_inv sg before )) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH46 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH47 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH48 : (timeout_pre <= UINT_MAX)) (PreH49 : (0 <= UINT_MAX)) (PreH50 : (timeout_pre >= 0)) (PreH51 : (0 >= 0)) (PreH52 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH53 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH54 : (pe = (event_addr (sg) (eid)))) (PreH55 : (valid_event_id sg eid )) (PreH56 : (q_query_public_slot before eid observed )) (PreH57 : (UCOS2_state_inv sg before )) (PreH58 : (pevent_pre <> 0)) (PreH59 : (pevent_pre = pe)) (PreH60 : (timeout_pre = ticks)) (PreH61 : (perr_pre = pd)) (PreH62 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH63 : (sem_pend_profile sg )) (PreH64 : (q_accept_profile sg )) (PreH65 : (kernel_tcb_stack_field_layout sg )) (PreH66 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH67 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH68 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH69 : (pe <> 0)) (PreH70 : (event_object_layout_prop sg eid )) (PreH71 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH72 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH73 : (0 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH74 : (2 <> (encode_pend_status ((node_2.(statPend) ))))) (PreH75 : (1 <> (encode_pend_status ((node_2.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed_2 retval resume_entry_2 cleaning_2 )
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
  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid 0 code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
.

Definition OSQPend_return_wit_1 := 
(
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before pmsg X )
) \/
(
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before pmsg X )
).

Definition OSQPend_return_wit_1_split_goal_spatial := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_restore_output None external platform environment critical saved_local sg resumed mask checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before pmsg X )
.

Definition OSQPend_return_wit_2 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_3)) + 4 ) = (queue_end_addr (q_3)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_3)))) (PreH5 : ((queue_entries (q_3)) <= 65535)) (PreH6 : (0 < (queue_entries (q_2)))) (PreH7 : ((queue_entries (q_2)) <= 65535)) (PreH8 : ((queue_entries (q)) > 0)) (PreH9 : (0 <= (queue_entries (q)))) (PreH10 : ((queue_entries (q)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before message X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_3)) + 4 ) = (queue_end_addr (q_3)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_3)))) (PreH5 : ((queue_entries (q_3)) <= 65535)) (PreH6 : (0 < (queue_entries (q_2)))) (PreH7 : ((queue_entries (q_2)) <= 65535)) (PreH8 : ((queue_entries (q)) > 0)) (PreH9 : (0 <= (queue_entries (q)))) (PreH10 : ((queue_entries (q)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before message X )
).

Definition OSQPend_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_3)) + 4 ) = (queue_end_addr (q_3)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_3)))) (PreH5 : ((queue_entries (q_3)) <= 65535)) (PreH6 : (0 < (queue_entries (q_2)))) (PreH7 : ((queue_entries (q_2)) <= 65535)) (PreH8 : ((queue_entries (q)) > 0)) (PreH9 : (0 <= (queue_entries (q)))) (PreH10 : ((queue_entries (q)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before message X )
.

Definition OSQPend_return_wit_3 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_3)) + 4 ) <> (queue_end_addr (q_3)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_3)))) (PreH5 : ((queue_entries (q_3)) <= 65535)) (PreH6 : (0 < (queue_entries (q_2)))) (PreH7 : ((queue_entries (q_2)) <= 65535)) (PreH8 : ((queue_entries (q)) > 0)) (PreH9 : (0 <= (queue_entries (q)))) (PreH10 : ((queue_entries (q)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before message X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_3)) + 4 ) <> (queue_end_addr (q_3)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_3)))) (PreH5 : ((queue_entries (q_3)) <= 65535)) (PreH6 : (0 < (queue_entries (q_2)))) (PreH7 : ((queue_entries (q_2)) <= 65535)) (PreH8 : ((queue_entries (q)) > 0)) (PreH9 : (0 <= (queue_entries (q)))) (PreH10 : ((queue_entries (q)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before message X )
).

Definition OSQPend_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_3)) + 4 ) <> (queue_end_addr (q_3)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_3)))) (PreH5 : ((queue_entries (q_3)) <= 65535)) (PreH6 : (0 < (queue_entries (q_2)))) (PreH7 : ((queue_entries (q_2)) <= 65535)) (PreH8 : ((queue_entries (q)) > 0)) (PreH9 : (0 <= (queue_entries (q)))) (PreH10 : ((queue_entries (q)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output None external platform environment critical saved_local sg entered mask checkpoint )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before message X )
.

Definition OSQPend_return_wit_4 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (q_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (q_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSQPend_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (q_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 13)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSQPend_return_wit_5 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSQPend_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(intNesting) ) > 0)) (PreH2 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH3 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (timeout_pre <= UINT_MAX)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (timeout_pre >= 0)) (PreH13 : (0 >= 0)) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (timeout_pre = ticks)) (PreH23 : (perr_pre = pd)) (PreH24 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH25 : (sem_pend_profile sg )) (PreH26 : (q_accept_profile sg )) (PreH27 : (kernel_tcb_stack_field_layout sg )) (PreH28 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH29 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH30 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH31 : (pe <> 0)) (PreH32 : (event_object_layout_prop sg eid )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 2)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSQPend_return_wit_6 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (q_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (q_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSQPend_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (q_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSQPend_return_wit_7 := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
).

Definition OSQPend_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe = 0)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (q_pend_api_post external platform environment critical saved_local sg context mask pe eid ticks pd before 0 X )
.

Definition OSQPend_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe <> 0)) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ”
.

Definition OSQPend_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (timeout_pre = ticks)) (PreH4 : (perr_pre = pd)) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (sem_pend_profile sg )) (PreH7 : (q_accept_profile sg )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH11 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH12 : (pe <> 0)) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (timeout_pre = ticks) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (sem_pend_profile sg ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_1 := OSQPend_partial_solve_wit_1_pure -> OSQPend_partial_solve_wit_1_aux.

Definition OSQPend_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (q_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
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

Definition OSQPend_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (timeout_pre <= UINT_MAX)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (timeout_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_query_public_slot before eid observed )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (timeout_pre = ticks)) (PreH17 : (perr_pre = pd)) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (sem_pend_profile sg )) (PreH20 : (q_accept_profile sg )) (PreH21 : (kernel_tcb_stack_field_layout sg )) (PreH22 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH23 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH24 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH25 : (pe <> 0)) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
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

Definition OSQPend_partial_solve_wit_2 := OSQPend_partial_solve_wit_2_pure -> OSQPend_partial_solve_wit_2_aux.

Definition OSQPend_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (q_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQPend_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH2 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH4 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH13 : (timeout_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (timeout_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH18 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (valid_event_id sg eid )) (PreH21 : (q_query_public_slot before eid observed )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (timeout_pre = ticks)) (PreH26 : (perr_pre = pd)) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (sem_pend_profile sg )) (PreH29 : (q_accept_profile sg )) (PreH30 : (kernel_tcb_stack_field_layout sg )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH33 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH34 : (pe <> 0)) (PreH35 : (event_object_layout_prop sg eid )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
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
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
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

Definition OSQPend_partial_solve_wit_3 := OSQPend_partial_solve_wit_3_pure -> OSQPend_partial_solve_wit_3_aux.

Definition OSQPend_partial_solve_wit_4 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (q_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_input (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_save_input (QueuePendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (q_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_output (QueuePendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQPend_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH4 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH5 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH8 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (timeout_pre <= UINT_MAX)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (timeout_pre >= 0)) (PreH18 : (0 >= 0)) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_query_public_slot before eid observed )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (timeout_pre = ticks)) (PreH28 : (perr_pre = pd)) (PreH29 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH30 : (sem_pend_profile sg )) (PreH31 : (q_accept_profile sg )) (PreH32 : (kernel_tcb_stack_field_layout sg )) (PreH33 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH34 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH35 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH36 : (pe <> 0)) (PreH37 : (event_object_layout_prop sg eid )) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_output (QueuePendAcquirePhase ((event_addr (sg) (eid))) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_save_output (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask retval before )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_5 := OSQPend_partial_solve_wit_5_pure -> OSQPend_partial_solve_wit_5_aux.

Definition OSQPend_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (current: OSEventAbstractState) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH6 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH7 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH9 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (timeout_pre <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (timeout_pre >= 0)) (PreH19 : (0 >= 0)) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (timeout_pre = ticks)) (PreH29 : (perr_pre = pd)) (PreH30 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH31 : (sem_pend_profile sg )) (PreH32 : (q_accept_profile sg )) (PreH33 : (kernel_tcb_stack_field_layout sg )) (PreH34 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH35 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH36 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH37 : (pe <> 0)) (PreH38 : (event_object_layout_prop sg eid )) (PreH39 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQPend_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (current: OSEventAbstractState) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH5 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH6 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH7 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH9 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (timeout_pre <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (timeout_pre >= 0)) (PreH19 : (0 >= 0)) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (timeout_pre = ticks)) (PreH29 : (perr_pre = pd)) (PreH30 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH31 : (sem_pend_profile sg )) (PreH32 : (q_accept_profile sg )) (PreH33 : (kernel_tcb_stack_field_layout sg )) (PreH34 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH35 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH36 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH37 : (pe <> 0)) (PreH38 : (event_object_layout_prop sg eid )) (PreH39 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_6 := OSQPend_partial_solve_wit_6_pure -> OSQPend_partial_solve_wit_6_aux.

Definition OSQPend_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_api_prefix pe before eid )) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH9 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH11 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH12 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH19 : (timeout_pre <= UINT_MAX)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (timeout_pre >= 0)) (PreH22 : (0 >= 0)) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_query_public_slot before eid observed )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (timeout_pre = ticks)) (PreH32 : (perr_pre = pd)) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (sem_pend_profile sg )) (PreH35 : (q_accept_profile sg )) (PreH36 : (kernel_tcb_stack_field_layout sg )) (PreH37 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH39 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH40 : (pe <> 0)) (PreH41 : (event_object_layout_prop sg eid )) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) > 0) ”
.

Definition OSQPend_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_api_prefix pe before eid )) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH9 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH11 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH12 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH19 : (timeout_pre <= UINT_MAX)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (timeout_pre >= 0)) (PreH22 : (0 >= 0)) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_query_public_slot before eid observed )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (timeout_pre = ticks)) (PreH32 : (perr_pre = pd)) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (sem_pend_profile sg )) (PreH35 : (q_accept_profile sg )) (PreH36 : (kernel_tcb_stack_field_layout sg )) (PreH37 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH39 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH40 : (pe <> 0)) (PreH41 : (event_object_layout_prop sg eid )) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) > 0) ” 
  &&  “ ((queue_entries (q)) > 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_7 := OSQPend_partial_solve_wit_7_pure -> OSQPend_partial_solve_wit_7_aux.

Definition OSQPend_partial_solve_wit_8 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (message: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q_3: QueueFields) (PreH1 : (0 < (queue_entries (q_3)))) (PreH2 : ((queue_entries (q_3)) <= 65535)) (PreH3 : ((queue_entries (q_2)) > 0)) (PreH4 : (0 <= (queue_entries (q_2)))) (PreH5 : ((queue_entries (q_2)) <= 65535)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (q_pend_api_prefix pe before eid )) (PreH8 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH9 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH10 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH11 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH12 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH13 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH18 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH19 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH20 : (timeout_pre <= UINT_MAX)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (timeout_pre >= 0)) (PreH23 : (0 >= 0)) (PreH24 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH25 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (valid_event_id sg eid )) (PreH28 : (q_query_public_slot before eid observed )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (timeout_pre = ticks)) (PreH33 : (perr_pre = pd)) (PreH34 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH35 : (sem_pend_profile sg )) (PreH36 : (q_accept_profile sg )) (PreH37 : (kernel_tcb_stack_field_layout sg )) (PreH38 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH40 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH41 : (pe <> 0)) (PreH42 : (event_object_layout_prop sg eid )) (PreH43 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH44 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q_3 next free slots (qcb_addr (sg) ((qID (q)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_3)) + (1 * sizeof(PTR))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_3)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_3 )
  **  (((queue_out_addr (q_3))) # Ptr  |-> message)
  **  (q_accept_head_slot q_3 slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 < (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q_3 next free slots (qcb_addr (sg) ((qID (q)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_3)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_3)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_3 )
  **  (((queue_out_addr (q_3))) # Ptr  |-> message)
  **  (q_accept_head_slot q_3 slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_9_pure := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_api_prefix pe before eid )) (PreH12 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH13 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH15 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH16 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH22 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH24 : (timeout_pre <= UINT_MAX)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (timeout_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH30 : (pe = (event_addr (sg) (eid)))) (PreH31 : (valid_event_id sg eid )) (PreH32 : (q_query_public_slot before eid observed )) (PreH33 : (UCOS2_state_inv sg before )) (PreH34 : (pevent_pre <> 0)) (PreH35 : (pevent_pre = pe)) (PreH36 : (timeout_pre = ticks)) (PreH37 : (perr_pre = pd)) (PreH38 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH39 : (sem_pend_profile sg )) (PreH40 : (q_accept_profile sg )) (PreH41 : (kernel_tcb_stack_field_layout sg )) (PreH42 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH43 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH44 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH45 : (pe <> 0)) (PreH46 : (event_object_layout_prop sg eid )) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ”
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_api_prefix pe before eid )) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH15 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH24 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH26 : (timeout_pre <= UINT_MAX)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (timeout_pre >= 0)) (PreH29 : (0 >= 0)) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (pe = (event_addr (sg) (eid)))) (PreH33 : (valid_event_id sg eid )) (PreH34 : (q_query_public_slot before eid observed )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (pevent_pre = pe)) (PreH38 : (timeout_pre = ticks)) (PreH39 : (perr_pre = pd)) (PreH40 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH41 : (sem_pend_profile sg )) (PreH42 : (q_accept_profile sg )) (PreH43 : (kernel_tcb_stack_field_layout sg )) (PreH44 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH45 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH46 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH47 : (pe <> 0)) (PreH48 : (event_object_layout_prop sg eid )) (PreH49 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH50 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ”
).

Definition OSQPend_partial_solve_wit_9_pure_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_api_prefix pe before eid )) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH15 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH24 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH26 : (timeout_pre <= UINT_MAX)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (timeout_pre >= 0)) (PreH29 : (0 >= 0)) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (pe = (event_addr (sg) (eid)))) (PreH33 : (valid_event_id sg eid )) (PreH34 : (q_query_public_slot before eid observed )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (pevent_pre = pe)) (PreH38 : (timeout_pre = ticks)) (PreH39 : (perr_pre = pd)) (PreH40 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH41 : (sem_pend_profile sg )) (PreH42 : (q_accept_profile sg )) (PreH43 : (kernel_tcb_stack_field_layout sg )) (PreH44 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH45 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH46 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH47 : (pe <> 0)) (PreH48 : (event_object_layout_prop sg eid )) (PreH49 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH50 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ”
.

Definition OSQPend_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_api_prefix pe before eid )) (PreH12 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH13 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH15 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH16 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH22 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH24 : (timeout_pre <= UINT_MAX)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (timeout_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH30 : (pe = (event_addr (sg) (eid)))) (PreH31 : (valid_event_id sg eid )) (PreH32 : (q_query_public_slot before eid observed )) (PreH33 : (UCOS2_state_inv sg before )) (PreH34 : (pevent_pre <> 0)) (PreH35 : (pevent_pre = pe)) (PreH36 : (timeout_pre = ticks)) (PreH37 : (perr_pre = pd)) (PreH38 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH39 : (sem_pend_profile sg )) (PreH40 : (q_accept_profile sg )) (PreH41 : (kernel_tcb_stack_field_layout sg )) (PreH42 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH43 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH44 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH45 : (pe <> 0)) (PreH46 : (event_object_layout_prop sg eid )) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ” 
  &&  “ (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ ((queue_entries (q_3)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_9 := OSQPend_partial_solve_wit_9_pure -> OSQPend_partial_solve_wit_9_aux.

Definition OSQPend_partial_solve_wit_10_pure := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_api_prefix pe before eid )) (PreH12 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH13 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH15 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH16 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH22 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH24 : (timeout_pre <= UINT_MAX)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (timeout_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH30 : (pe = (event_addr (sg) (eid)))) (PreH31 : (valid_event_id sg eid )) (PreH32 : (q_query_public_slot before eid observed )) (PreH33 : (UCOS2_state_inv sg before )) (PreH34 : (pevent_pre <> 0)) (PreH35 : (pevent_pre = pe)) (PreH36 : (timeout_pre = ticks)) (PreH37 : (perr_pre = pd)) (PreH38 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH39 : (sem_pend_profile sg )) (PreH40 : (q_accept_profile sg )) (PreH41 : (kernel_tcb_stack_field_layout sg )) (PreH42 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH43 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH44 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH45 : (pe <> 0)) (PreH46 : (event_object_layout_prop sg eid )) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ”
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_api_prefix pe before eid )) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH15 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH24 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH26 : (timeout_pre <= UINT_MAX)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (timeout_pre >= 0)) (PreH29 : (0 >= 0)) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (pe = (event_addr (sg) (eid)))) (PreH33 : (valid_event_id sg eid )) (PreH34 : (q_query_public_slot before eid observed )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (pevent_pre = pe)) (PreH38 : (timeout_pre = ticks)) (PreH39 : (perr_pre = pd)) (PreH40 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH41 : (sem_pend_profile sg )) (PreH42 : (q_accept_profile sg )) (PreH43 : (kernel_tcb_stack_field_layout sg )) (PreH44 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH45 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH46 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH47 : (pe <> 0)) (PreH48 : (event_object_layout_prop sg eid )) (PreH49 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH50 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ”
).

Definition OSQPend_partial_solve_wit_10_pure_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (q_pend_api_prefix pe before eid )) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH15 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH16 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH18 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH19 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH24 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH25 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH26 : (timeout_pre <= UINT_MAX)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (timeout_pre >= 0)) (PreH29 : (0 >= 0)) (PreH30 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH31 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH32 : (pe = (event_addr (sg) (eid)))) (PreH33 : (valid_event_id sg eid )) (PreH34 : (q_query_public_slot before eid observed )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (pevent_pre = pe)) (PreH38 : (timeout_pre = ticks)) (PreH39 : (perr_pre = pd)) (PreH40 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH41 : (sem_pend_profile sg )) (PreH42 : (q_accept_profile sg )) (PreH43 : (kernel_tcb_stack_field_layout sg )) (PreH44 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH45 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH46 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH47 : (pe <> 0)) (PreH48 : (event_object_layout_prop sg eid )) (PreH49 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH50 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ”
.

Definition OSQPend_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (current: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_api_prefix pe before eid )) (PreH12 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH13 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH14 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH15 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH16 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH17 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH22 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH23 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH24 : (timeout_pre <= UINT_MAX)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (timeout_pre >= 0)) (PreH27 : (0 >= 0)) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH30 : (pe = (event_addr (sg) (eid)))) (PreH31 : (valid_event_id sg eid )) (PreH32 : (q_query_public_slot before eid observed )) (PreH33 : (UCOS2_state_inv sg before )) (PreH34 : (pevent_pre <> 0)) (PreH35 : (pevent_pre = pe)) (PreH36 : (timeout_pre = ticks)) (PreH37 : (perr_pre = pd)) (PreH38 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH39 : (sem_pend_profile sg )) (PreH40 : (q_accept_profile sg )) (PreH41 : (kernel_tcb_stack_field_layout sg )) (PreH42 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH43 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH44 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH45 : (pe <> 0)) (PreH46 : (event_object_layout_prop sg eid )) (PreH47 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH48 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ” 
  &&  “ (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ ((queue_entries (q_3)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q next free slots (qcb_addr (sg) ((qID (q_2)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_10 := OSQPend_partial_solve_wit_10_pure -> OSQPend_partial_solve_wit_10_aux.

Definition OSQPend_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_4)))) (PreH5 : ((queue_entries (q_4)) <= 65535)) (PreH6 : (0 < (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : ((queue_entries (q_2)) > 0)) (PreH9 : (0 <= (queue_entries (q_2)))) (PreH10 : ((queue_entries (q_2)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSQPend_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_4)))) (PreH5 : ((queue_entries (q_4)) <= 65535)) (PreH6 : (0 < (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : ((queue_entries (q_2)) > 0)) (PreH9 : (0 <= (queue_entries (q_2)))) (PreH10 : ((queue_entries (q_2)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint ) ” 
  &&  “ (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_11 := OSQPend_partial_solve_wit_11_pure -> OSQPend_partial_solve_wit_11_aux.

Definition OSQPend_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_4)))) (PreH5 : ((queue_entries (q_4)) <= 65535)) (PreH6 : (0 < (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : ((queue_entries (q_2)) > 0)) (PreH9 : (0 <= (queue_entries (q_2)))) (PreH10 : ((queue_entries (q_2)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSQPend_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint )) (PreH2 : (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4)))) (PreH3 : (message = message_2)) (PreH4 : (0 < (queue_entries (q_4)))) (PreH5 : ((queue_entries (q_4)) <= 65535)) (PreH6 : (0 < (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : ((queue_entries (q_2)) > 0)) (PreH9 : (0 <= (queue_entries (q_2)))) (PreH10 : ((queue_entries (q_2)) <= 65535)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (q_pend_api_prefix pe before eid )) (PreH13 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH14 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH15 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH16 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH17 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH18 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH23 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH24 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH25 : (timeout_pre <= UINT_MAX)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (timeout_pre >= 0)) (PreH28 : (0 >= 0)) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH31 : (pe = (event_addr (sg) (eid)))) (PreH32 : (valid_event_id sg eid )) (PreH33 : (q_query_public_slot before eid observed )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (pevent_pre = pe)) (PreH37 : (timeout_pre = ticks)) (PreH38 : (perr_pre = pd)) (PreH39 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH40 : (sem_pend_profile sg )) (PreH41 : (q_accept_profile sg )) (PreH42 : (kernel_tcb_stack_field_layout sg )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH45 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH46 : (pe <> 0)) (PreH47 : (event_object_layout_prop sg eid )) (PreH48 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH49 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint ) ” 
  &&  “ (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_restore_input None external platform environment critical saved_local sg entered mask retval entry checkpoint )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_12 := OSQPend_partial_solve_wit_12_pure -> OSQPend_partial_solve_wit_12_aux.

Definition OSQPend_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_api_prefix pe before eid )) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH9 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH11 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH12 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH19 : (timeout_pre <= UINT_MAX)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (timeout_pre >= 0)) (PreH22 : (0 >= 0)) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_query_public_slot before eid observed )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (timeout_pre = ticks)) (PreH32 : (perr_pre = pd)) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (sem_pend_profile sg )) (PreH35 : (q_accept_profile sg )) (PreH36 : (kernel_tcb_stack_field_layout sg )) (PreH37 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH39 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH40 : (pe <> 0)) (PreH41 : (event_object_layout_prop sg eid )) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSQPend_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (q: QueueFields) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_api_prefix pe before eid )) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH9 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH10 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH11 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH12 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH19 : (timeout_pre <= UINT_MAX)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (timeout_pre >= 0)) (PreH22 : (0 >= 0)) (PreH23 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH24 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_query_public_slot before eid observed )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (timeout_pre = ticks)) (PreH32 : (perr_pre = pd)) (PreH33 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH34 : (sem_pend_profile sg )) (PreH35 : (q_accept_profile sg )) (PreH36 : (kernel_tcb_stack_field_layout sg )) (PreH37 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH38 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH39 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH40 : (pe <> 0)) (PreH41 : (event_object_layout_prop sg eid )) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  (q_pend_first_owner external platform environment critical saved_local sg context entered mask retval pe before entry eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask retval before entry eid observed current q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_13 := OSQPend_partial_solve_wit_13_pure -> OSQPend_partial_solve_wit_13_aux.

Definition OSQPend_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH2 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH3 : ((old.(dly) ) <= UINT_MAX)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (ticks <= UINT_MAX)) (PreH6 : ((old.(dly) ) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (ticks >= 0)) (PreH9 : (environment = (Some (owned)))) (PreH10 : (external = (task_stack_call_external (owned)))) (PreH11 : (platform = (task_stack_call_platform (owned)))) (PreH12 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH13 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH14 : ((queue_entries (q_2)) <= 0)) (PreH15 : (0 <= (queue_entries (q_2)))) (PreH16 : ((queue_entries (q_2)) <= 65535)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (q_pend_api_prefix pe before eid )) (PreH19 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH20 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH22 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH29 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH31 : (timeout_pre <= UINT_MAX)) (PreH32 : (0 <= UINT_MAX)) (PreH33 : (timeout_pre >= 0)) (PreH34 : (0 >= 0)) (PreH35 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH36 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH37 : (pe = (event_addr (sg) (eid)))) (PreH38 : (valid_event_id sg eid )) (PreH39 : (q_query_public_slot before eid observed )) (PreH40 : (UCOS2_state_inv sg before )) (PreH41 : (pevent_pre <> 0)) (PreH42 : (pevent_pre = pe)) (PreH43 : (timeout_pre = ticks)) (PreH44 : (perr_pre = pd)) (PreH45 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH46 : (sem_pend_profile sg )) (PreH47 : (q_accept_profile sg )) (PreH48 : (kernel_tcb_stack_field_layout sg )) (PreH49 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH50 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH51 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH52 : (pe <> 0)) (PreH53 : (event_object_layout_prop sg eid )) (PreH54 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH55 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQPend_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH2 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH3 : ((old.(dly) ) <= UINT_MAX)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (ticks <= UINT_MAX)) (PreH6 : ((old.(dly) ) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (ticks >= 0)) (PreH9 : (environment = (Some (owned)))) (PreH10 : (external = (task_stack_call_external (owned)))) (PreH11 : (platform = (task_stack_call_platform (owned)))) (PreH12 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH13 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH14 : ((queue_entries (q_2)) <= 0)) (PreH15 : (0 <= (queue_entries (q_2)))) (PreH16 : ((queue_entries (q_2)) <= 65535)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (q_pend_api_prefix pe before eid )) (PreH19 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH20 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH22 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH29 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH31 : (timeout_pre <= UINT_MAX)) (PreH32 : (0 <= UINT_MAX)) (PreH33 : (timeout_pre >= 0)) (PreH34 : (0 >= 0)) (PreH35 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH36 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH37 : (pe = (event_addr (sg) (eid)))) (PreH38 : (valid_event_id sg eid )) (PreH39 : (q_query_public_slot before eid observed )) (PreH40 : (UCOS2_state_inv sg before )) (PreH41 : (pevent_pre <> 0)) (PreH42 : (pevent_pre = pe)) (PreH43 : (timeout_pre = ticks)) (PreH44 : (perr_pre = pd)) (PreH45 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH46 : (sem_pend_profile sg )) (PreH47 : (q_accept_profile sg )) (PreH48 : (kernel_tcb_stack_field_layout sg )) (PreH49 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH50 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH51 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH52 : (pe <> 0)) (PreH53 : (event_object_layout_prop sg eid )) (PreH54 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH55 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
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
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_14 := OSQPend_partial_solve_wit_14_pure -> OSQPend_partial_solve_wit_14_aux.

Definition OSQPend_partial_solve_wit_15_pure := 
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ”
) \/
(
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : (environment = (Some (owned)))) (PreH12 : (external = (task_stack_call_external (owned)))) (PreH13 : (platform = (task_stack_call_platform (owned)))) (PreH14 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH15 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH16 : ((queue_entries (q_2)) <= 0)) (PreH17 : (0 <= (queue_entries (q_2)))) (PreH18 : ((queue_entries (q_2)) <= 65535)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (q_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (q_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ”
).

Definition OSQPend_partial_solve_wit_15_pure_split_goal_1 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : (environment = (Some (owned)))) (PreH12 : (external = (task_stack_call_external (owned)))) (PreH13 : (platform = (task_stack_call_platform (owned)))) (PreH14 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH15 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH16 : ((queue_entries (q_2)) <= 0)) (PreH17 : (0 <= (queue_entries (q_2)))) (PreH18 : ((queue_entries (q_2)) <= 65535)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (q_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (q_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ”
.

Definition OSQPend_partial_solve_wit_15_pure_split_goal_2 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : (environment = (Some (owned)))) (PreH12 : (external = (task_stack_call_external (owned)))) (PreH13 : (platform = (task_stack_call_platform (owned)))) (PreH14 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH15 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH16 : ((queue_entries (q_2)) <= 0)) (PreH17 : (0 <= (queue_entries (q_2)))) (PreH18 : ((queue_entries (q_2)) <= 65535)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (q_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (q_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_pend_wait_call_pre sg entry eid current tid old ticks )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ”
.

Definition OSQPend_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_wait_call_pre sg entry eid current tid old ticks )
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (sg.(g_OSRdyTbl) )) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (sg.(g_OSRdyGrp) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_wait_call_pre sg entry eid current tid old ticks )
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_15 := OSQPend_partial_solve_wit_15_pure -> OSQPend_partial_solve_wit_15_aux.

Definition OSQPend_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : (environment = (Some (owned)))) (PreH12 : (external = (task_stack_call_external (owned)))) (PreH13 : (platform = (task_stack_call_platform (owned)))) (PreH14 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH15 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH16 : ((queue_entries (q_2)) <= 0)) (PreH17 : (0 <= (queue_entries (q_2)))) (PreH18 : ((queue_entries (q_2)) <= 65535)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (q_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (q_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_wait_call_post sg entry eid current tid old ticks )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
.

Definition OSQPend_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH2 : (q_pend_wait_entry sg entry eid current tid old )) (PreH3 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH4 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH5 : ((old.(dly) ) <= UINT_MAX)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (ticks <= UINT_MAX)) (PreH8 : ((old.(dly) ) >= 0)) (PreH9 : (retval >= 0)) (PreH10 : (ticks >= 0)) (PreH11 : (environment = (Some (owned)))) (PreH12 : (external = (task_stack_call_external (owned)))) (PreH13 : (platform = (task_stack_call_platform (owned)))) (PreH14 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH15 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH16 : ((queue_entries (q_2)) <= 0)) (PreH17 : (0 <= (queue_entries (q_2)))) (PreH18 : ((queue_entries (q_2)) <= 65535)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (q_pend_api_prefix pe before eid )) (PreH21 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH22 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH23 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH24 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH26 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH31 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH32 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH33 : (timeout_pre <= UINT_MAX)) (PreH34 : (0 <= UINT_MAX)) (PreH35 : (timeout_pre >= 0)) (PreH36 : (0 >= 0)) (PreH37 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH38 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH39 : (pe = (event_addr (sg) (eid)))) (PreH40 : (valid_event_id sg eid )) (PreH41 : (q_query_public_slot before eid observed )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : (pevent_pre <> 0)) (PreH44 : (pevent_pre = pe)) (PreH45 : (timeout_pre = ticks)) (PreH46 : (perr_pre = pd)) (PreH47 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH48 : (sem_pend_profile sg )) (PreH49 : (q_accept_profile sg )) (PreH50 : (kernel_tcb_stack_field_layout sg )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH53 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH54 : (pe <> 0)) (PreH55 : (event_object_layout_prop sg eid )) (PreH56 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH57 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_wait_call_post sg entry eid current tid old ticks )
  **  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg entered retval entry entry )
  **  (q_pend_wait_call_post sg entry eid current tid old ticks )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_16 := OSQPend_partial_solve_wit_16_pure -> OSQPend_partial_solve_wit_16_aux.

Definition OSQPend_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH2 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (q_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_pend_restore_input (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask retval entry waiting )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSQPend_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH2 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (q_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_input (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask retval entry waiting )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_restore_input (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask retval entry waiting )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_17 := OSQPend_partial_solve_wit_17_pure -> OSQPend_partial_solve_wit_17_aux.

Definition OSQPend_partial_solve_wit_18_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH2 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (q_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask waiting )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ”
.

Definition OSQPend_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH2 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH3 : (q_pend_wait_entry sg entry eid current tid old )) (PreH4 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH5 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH6 : ((old.(dly) ) <= UINT_MAX)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (ticks <= UINT_MAX)) (PreH9 : ((old.(dly) ) >= 0)) (PreH10 : (retval >= 0)) (PreH11 : (ticks >= 0)) (PreH12 : (environment = (Some (owned)))) (PreH13 : (external = (task_stack_call_external (owned)))) (PreH14 : (platform = (task_stack_call_platform (owned)))) (PreH15 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH16 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH17 : ((queue_entries (q_2)) <= 0)) (PreH18 : (0 <= (queue_entries (q_2)))) (PreH19 : ((queue_entries (q_2)) <= 65535)) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (q_pend_api_prefix pe before eid )) (PreH22 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH23 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH25 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH32 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH34 : (timeout_pre <= UINT_MAX)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (timeout_pre >= 0)) (PreH37 : (0 >= 0)) (PreH38 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH39 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH40 : (pe = (event_addr (sg) (eid)))) (PreH41 : (valid_event_id sg eid )) (PreH42 : (q_query_public_slot before eid observed )) (PreH43 : (UCOS2_state_inv sg before )) (PreH44 : (pevent_pre <> 0)) (PreH45 : (pevent_pre = pe)) (PreH46 : (timeout_pre = ticks)) (PreH47 : (perr_pre = pd)) (PreH48 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH49 : (sem_pend_profile sg )) (PreH50 : (q_accept_profile sg )) (PreH51 : (kernel_tcb_stack_field_layout sg )) (PreH52 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH53 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH54 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH55 : (pe <> 0)) (PreH56 : (event_object_layout_prop sg eid )) (PreH57 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH58 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_restore_output (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg entered mask waiting )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_restore_output (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask waiting )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_18 := OSQPend_partial_solve_wit_18_pure -> OSQPend_partial_solve_wit_18_aux.

Definition OSQPend_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (PreH1 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH2 : (q_pend_sched_admitted environment critical )) (PreH3 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH4 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH5 : (q_pend_wait_entry sg entry eid current tid old )) (PreH6 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH7 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH8 : ((old.(dly) ) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : (ticks <= UINT_MAX)) (PreH11 : ((old.(dly) ) >= 0)) (PreH12 : (retval >= 0)) (PreH13 : (ticks >= 0)) (PreH14 : (environment = (Some (owned)))) (PreH15 : (external = (task_stack_call_external (owned)))) (PreH16 : (platform = (task_stack_call_platform (owned)))) (PreH17 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH18 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH19 : ((queue_entries (q_2)) <= 0)) (PreH20 : (0 <= (queue_entries (q_2)))) (PreH21 : ((queue_entries (q_2)) <= 65535)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (q_pend_api_prefix pe before eid )) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH28 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH32 : (UCOS2_state_inv sg before )) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH34 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH36 : (timeout_pre <= UINT_MAX)) (PreH37 : (0 <= UINT_MAX)) (PreH38 : (timeout_pre >= 0)) (PreH39 : (0 >= 0)) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH42 : (pe = (event_addr (sg) (eid)))) (PreH43 : (valid_event_id sg eid )) (PreH44 : (q_query_public_slot before eid observed )) (PreH45 : (UCOS2_state_inv sg before )) (PreH46 : (pevent_pre <> 0)) (PreH47 : (pevent_pre = pe)) (PreH48 : (timeout_pre = ticks)) (PreH49 : (perr_pre = pd)) (PreH50 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH51 : (sem_pend_profile sg )) (PreH52 : (q_accept_profile sg )) (PreH53 : (kernel_tcb_stack_field_layout sg )) (PreH54 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH55 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH56 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH57 : (pe <> 0)) (PreH58 : (event_object_layout_prop sg eid )) (PreH59 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH60 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_continuation_phase_sched_input (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQPend_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (PreH1 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH2 : (q_pend_sched_admitted environment critical )) (PreH3 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH4 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH5 : (q_pend_wait_entry sg entry eid current tid old )) (PreH6 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH7 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH8 : ((old.(dly) ) <= UINT_MAX)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : (ticks <= UINT_MAX)) (PreH11 : ((old.(dly) ) >= 0)) (PreH12 : (retval >= 0)) (PreH13 : (ticks >= 0)) (PreH14 : (environment = (Some (owned)))) (PreH15 : (external = (task_stack_call_external (owned)))) (PreH16 : (platform = (task_stack_call_platform (owned)))) (PreH17 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH18 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH19 : ((queue_entries (q_2)) <= 0)) (PreH20 : (0 <= (queue_entries (q_2)))) (PreH21 : ((queue_entries (q_2)) <= 65535)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (q_pend_api_prefix pe before eid )) (PreH24 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH25 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH27 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH28 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH32 : (UCOS2_state_inv sg before )) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH34 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH36 : (timeout_pre <= UINT_MAX)) (PreH37 : (0 <= UINT_MAX)) (PreH38 : (timeout_pre >= 0)) (PreH39 : (0 >= 0)) (PreH40 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH41 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH42 : (pe = (event_addr (sg) (eid)))) (PreH43 : (valid_event_id sg eid )) (PreH44 : (q_query_public_slot before eid observed )) (PreH45 : (UCOS2_state_inv sg before )) (PreH46 : (pevent_pre <> 0)) (PreH47 : (pevent_pre = pe)) (PreH48 : (timeout_pre = ticks)) (PreH49 : (perr_pre = pd)) (PreH50 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH51 : (sem_pend_profile sg )) (PreH52 : (q_accept_profile sg )) (PreH53 : (kernel_tcb_stack_field_layout sg )) (PreH54 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH55 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH56 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH57 : (pe <> 0)) (PreH58 : (event_object_layout_prop sg eid )) (PreH59 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH60 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_continuation_phase_sched_input (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_continuation_phase_sched_input (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_19 := OSQPend_partial_solve_wit_19_pure -> OSQPend_partial_solve_wit_19_aux.

Definition OSQPend_partial_solve_wit_20_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH3 : (q_pend_sched_admitted environment critical )) (PreH4 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH5 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH6 : (q_pend_wait_entry sg entry eid current tid old )) (PreH7 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH8 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH9 : ((old.(dly) ) <= UINT_MAX)) (PreH10 : (retval <= UINT_MAX)) (PreH11 : (ticks <= UINT_MAX)) (PreH12 : ((old.(dly) ) >= 0)) (PreH13 : (retval >= 0)) (PreH14 : (ticks >= 0)) (PreH15 : (environment = (Some (owned)))) (PreH16 : (external = (task_stack_call_external (owned)))) (PreH17 : (platform = (task_stack_call_platform (owned)))) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH20 : ((queue_entries (q_2)) <= 0)) (PreH21 : (0 <= (queue_entries (q_2)))) (PreH22 : ((queue_entries (q_2)) <= 65535)) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (q_pend_api_prefix pe before eid )) (PreH25 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH27 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH28 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH29 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH30 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH33 : (UCOS2_state_inv sg before )) (PreH34 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH35 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH36 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH37 : (timeout_pre <= UINT_MAX)) (PreH38 : (0 <= UINT_MAX)) (PreH39 : (timeout_pre >= 0)) (PreH40 : (0 >= 0)) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH43 : (pe = (event_addr (sg) (eid)))) (PreH44 : (valid_event_id sg eid )) (PreH45 : (q_query_public_slot before eid observed )) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : (pevent_pre <> 0)) (PreH48 : (pevent_pre = pe)) (PreH49 : (timeout_pre = ticks)) (PreH50 : (perr_pre = pd)) (PreH51 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH52 : (sem_pend_profile sg )) (PreH53 : (q_accept_profile sg )) (PreH54 : (kernel_tcb_stack_field_layout sg )) (PreH55 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH56 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH57 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH58 : (pe <> 0)) (PreH59 : (event_object_layout_prop sg eid )) (PreH60 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH61 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_continuation_phase_sched_output (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ”
.

Definition OSQPend_partial_solve_wit_20_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH3 : (q_pend_sched_admitted environment critical )) (PreH4 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH5 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH6 : (q_pend_wait_entry sg entry eid current tid old )) (PreH7 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH8 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH9 : ((old.(dly) ) <= UINT_MAX)) (PreH10 : (retval <= UINT_MAX)) (PreH11 : (ticks <= UINT_MAX)) (PreH12 : ((old.(dly) ) >= 0)) (PreH13 : (retval >= 0)) (PreH14 : (ticks >= 0)) (PreH15 : (environment = (Some (owned)))) (PreH16 : (external = (task_stack_call_external (owned)))) (PreH17 : (platform = (task_stack_call_platform (owned)))) (PreH18 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH19 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH20 : ((queue_entries (q_2)) <= 0)) (PreH21 : (0 <= (queue_entries (q_2)))) (PreH22 : ((queue_entries (q_2)) <= 65535)) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (q_pend_api_prefix pe before eid )) (PreH25 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH26 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH27 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH28 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH29 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH30 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH32 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH33 : (UCOS2_state_inv sg before )) (PreH34 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH35 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH36 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH37 : (timeout_pre <= UINT_MAX)) (PreH38 : (0 <= UINT_MAX)) (PreH39 : (timeout_pre >= 0)) (PreH40 : (0 >= 0)) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH43 : (pe = (event_addr (sg) (eid)))) (PreH44 : (valid_event_id sg eid )) (PreH45 : (q_query_public_slot before eid observed )) (PreH46 : (UCOS2_state_inv sg before )) (PreH47 : (pevent_pre <> 0)) (PreH48 : (pevent_pre = pe)) (PreH49 : (timeout_pre = ticks)) (PreH50 : (perr_pre = pd)) (PreH51 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH52 : (sem_pend_profile sg )) (PreH53 : (q_accept_profile sg )) (PreH54 : (kernel_tcb_stack_field_layout sg )) (PreH55 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH56 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH57 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH58 : (pe <> 0)) (PreH59 : (event_object_layout_prop sg eid )) (PreH60 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH61 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_continuation_phase_sched_output (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_continuation_phase_sched_output (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_20 := OSQPend_partial_solve_wit_20_pure -> OSQPend_partial_solve_wit_20_aux.

Definition OSQPend_partial_solve_wit_21 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (PreH1 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH4 : (q_pend_sched_admitted environment critical )) (PreH5 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH6 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH7 : (q_pend_wait_entry sg entry eid current tid old )) (PreH8 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH9 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH10 : ((old.(dly) ) <= UINT_MAX)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (ticks <= UINT_MAX)) (PreH13 : ((old.(dly) ) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (ticks >= 0)) (PreH16 : (environment = (Some (owned)))) (PreH17 : (external = (task_stack_call_external (owned)))) (PreH18 : (platform = (task_stack_call_platform (owned)))) (PreH19 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH20 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH21 : ((queue_entries (q)) <= 0)) (PreH22 : (0 <= (queue_entries (q)))) (PreH23 : ((queue_entries (q)) <= 65535)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (q_pend_api_prefix pe before eid )) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH27 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH36 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH38 : (timeout_pre <= UINT_MAX)) (PreH39 : (0 <= UINT_MAX)) (PreH40 : (timeout_pre >= 0)) (PreH41 : (0 >= 0)) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (pe = (event_addr (sg) (eid)))) (PreH45 : (valid_event_id sg eid )) (PreH46 : (q_query_public_slot before eid observed )) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : (pevent_pre <> 0)) (PreH49 : (pevent_pre = pe)) (PreH50 : (timeout_pre = ticks)) (PreH51 : (perr_pre = pd)) (PreH52 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH53 : (sem_pend_profile sg )) (PreH54 : (q_accept_profile sg )) (PreH55 : (kernel_tcb_stack_field_layout sg )) (PreH56 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH57 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH58 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH59 : (pe <> 0)) (PreH60 : (event_object_layout_prop sg eid )) (PreH61 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH62 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_input (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg scheduled mask selected )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_save_input (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg scheduled mask selected )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH4 : (q_pend_sched_admitted environment critical )) (PreH5 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH6 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH7 : (q_pend_wait_entry sg entry eid current tid old )) (PreH8 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH9 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH10 : ((old.(dly) ) <= UINT_MAX)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (ticks <= UINT_MAX)) (PreH13 : ((old.(dly) ) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (ticks >= 0)) (PreH16 : (environment = (Some (owned)))) (PreH17 : (external = (task_stack_call_external (owned)))) (PreH18 : (platform = (task_stack_call_platform (owned)))) (PreH19 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH20 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH21 : ((queue_entries (q_2)) <= 0)) (PreH22 : (0 <= (queue_entries (q_2)))) (PreH23 : ((queue_entries (q_2)) <= 65535)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (q_pend_api_prefix pe before eid )) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH27 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH36 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH38 : (timeout_pre <= UINT_MAX)) (PreH39 : (0 <= UINT_MAX)) (PreH40 : (timeout_pre >= 0)) (PreH41 : (0 >= 0)) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (pe = (event_addr (sg) (eid)))) (PreH45 : (valid_event_id sg eid )) (PreH46 : (q_query_public_slot before eid observed )) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : (pevent_pre <> 0)) (PreH49 : (pevent_pre = pe)) (PreH50 : (timeout_pre = ticks)) (PreH51 : (perr_pre = pd)) (PreH52 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH53 : (sem_pend_profile sg )) (PreH54 : (q_accept_profile sg )) (PreH55 : (kernel_tcb_stack_field_layout sg )) (PreH56 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH57 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH58 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH59 : (pe <> 0)) (PreH60 : (event_object_layout_prop sg eid )) (PreH61 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH62 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_output (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg scheduled mask retval_2 selected )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSQPend_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH4 : (q_pend_sched_admitted environment critical )) (PreH5 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH6 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH7 : (q_pend_wait_entry sg entry eid current tid old )) (PreH8 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH9 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH10 : ((old.(dly) ) <= UINT_MAX)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (ticks <= UINT_MAX)) (PreH13 : ((old.(dly) ) >= 0)) (PreH14 : (retval >= 0)) (PreH15 : (ticks >= 0)) (PreH16 : (environment = (Some (owned)))) (PreH17 : (external = (task_stack_call_external (owned)))) (PreH18 : (platform = (task_stack_call_platform (owned)))) (PreH19 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH20 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH21 : ((queue_entries (q_2)) <= 0)) (PreH22 : (0 <= (queue_entries (q_2)))) (PreH23 : ((queue_entries (q_2)) <= 65535)) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (q_pend_api_prefix pe before eid )) (PreH26 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH27 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH28 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH29 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH31 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH36 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH37 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH38 : (timeout_pre <= UINT_MAX)) (PreH39 : (0 <= UINT_MAX)) (PreH40 : (timeout_pre >= 0)) (PreH41 : (0 >= 0)) (PreH42 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH43 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH44 : (pe = (event_addr (sg) (eid)))) (PreH45 : (valid_event_id sg eid )) (PreH46 : (q_query_public_slot before eid observed )) (PreH47 : (UCOS2_state_inv sg before )) (PreH48 : (pevent_pre <> 0)) (PreH49 : (pevent_pre = pe)) (PreH50 : (timeout_pre = ticks)) (PreH51 : (perr_pre = pd)) (PreH52 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH53 : (sem_pend_profile sg )) (PreH54 : (q_accept_profile sg )) (PreH55 : (kernel_tcb_stack_field_layout sg )) (PreH56 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH57 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH58 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH59 : (pe <> 0)) (PreH60 : (event_object_layout_prop sg eid )) (PreH61 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH62 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_pend_save_output (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg scheduled mask retval_2 selected )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_pend_save_output (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg scheduled mask retval_2 selected )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_22 := OSQPend_partial_solve_wit_22_pure -> OSQPend_partial_solve_wit_22_aux.

Definition OSQPend_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH12 : (q_pend_sched_admitted environment critical )) (PreH13 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH14 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH15 : (q_pend_wait_entry sg entry eid current_2 tid old )) (PreH16 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH17 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH18 : ((old.(dly) ) <= UINT_MAX)) (PreH19 : (retval <= UINT_MAX)) (PreH20 : (ticks <= UINT_MAX)) (PreH21 : ((old.(dly) ) >= 0)) (PreH22 : (retval >= 0)) (PreH23 : (ticks >= 0)) (PreH24 : (environment = (Some (owned)))) (PreH25 : (external = (task_stack_call_external (owned)))) (PreH26 : (platform = (task_stack_call_platform (owned)))) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH29 : ((queue_entries (q_2)) <= 0)) (PreH30 : (0 <= (queue_entries (q_2)))) (PreH31 : ((queue_entries (q_2)) <= 65535)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (q_pend_api_prefix pe before eid )) (PreH34 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH37 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH38 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH44 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH46 : (timeout_pre <= UINT_MAX)) (PreH47 : (0 <= UINT_MAX)) (PreH48 : (timeout_pre >= 0)) (PreH49 : (0 >= 0)) (PreH50 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (pe = (event_addr (sg) (eid)))) (PreH53 : (valid_event_id sg eid )) (PreH54 : (q_query_public_slot before eid observed )) (PreH55 : (UCOS2_state_inv sg before )) (PreH56 : (pevent_pre <> 0)) (PreH57 : (pevent_pre = pe)) (PreH58 : (timeout_pre = ticks)) (PreH59 : (perr_pre = pd)) (PreH60 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH61 : (sem_pend_profile sg )) (PreH62 : (q_accept_profile sg )) (PreH63 : (kernel_tcb_stack_field_layout sg )) (PreH64 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH65 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH66 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH67 : (pe <> 0)) (PreH68 : (event_object_layout_prop sg eid )) (PreH69 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH70 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH71 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH72 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH73 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSQPend_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH12 : (q_pend_sched_admitted environment critical )) (PreH13 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH14 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH15 : (q_pend_wait_entry sg entry eid current_2 tid old )) (PreH16 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH17 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH18 : ((old.(dly) ) <= UINT_MAX)) (PreH19 : (retval <= UINT_MAX)) (PreH20 : (ticks <= UINT_MAX)) (PreH21 : ((old.(dly) ) >= 0)) (PreH22 : (retval >= 0)) (PreH23 : (ticks >= 0)) (PreH24 : (environment = (Some (owned)))) (PreH25 : (external = (task_stack_call_external (owned)))) (PreH26 : (platform = (task_stack_call_platform (owned)))) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH29 : ((queue_entries (q_2)) <= 0)) (PreH30 : (0 <= (queue_entries (q_2)))) (PreH31 : ((queue_entries (q_2)) <= 65535)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (q_pend_api_prefix pe before eid )) (PreH34 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH37 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH38 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH44 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH46 : (timeout_pre <= UINT_MAX)) (PreH47 : (0 <= UINT_MAX)) (PreH48 : (timeout_pre >= 0)) (PreH49 : (0 >= 0)) (PreH50 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (pe = (event_addr (sg) (eid)))) (PreH53 : (valid_event_id sg eid )) (PreH54 : (q_query_public_slot before eid observed )) (PreH55 : (UCOS2_state_inv sg before )) (PreH56 : (pevent_pre <> 0)) (PreH57 : (pevent_pre = pe)) (PreH58 : (timeout_pre = ticks)) (PreH59 : (perr_pre = pd)) (PreH60 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH61 : (sem_pend_profile sg )) (PreH62 : (q_accept_profile sg )) (PreH63 : (kernel_tcb_stack_field_layout sg )) (PreH64 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH65 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH66 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH67 : (pe <> 0)) (PreH68 : (event_object_layout_prop sg eid )) (PreH69 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH70 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH71 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH72 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH73 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
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
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current_2 tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 <> (encode_pend_status ((node.(statPend) )))) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_23 := OSQPend_partial_solve_wit_23_pure -> OSQPend_partial_solve_wit_23_aux.

Definition OSQPend_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH12 : (q_pend_sched_admitted environment critical )) (PreH13 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH14 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH15 : (q_pend_wait_entry sg entry eid current_2 tid old )) (PreH16 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH17 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH18 : ((old.(dly) ) <= UINT_MAX)) (PreH19 : (retval <= UINT_MAX)) (PreH20 : (ticks <= UINT_MAX)) (PreH21 : ((old.(dly) ) >= 0)) (PreH22 : (retval >= 0)) (PreH23 : (ticks >= 0)) (PreH24 : (environment = (Some (owned)))) (PreH25 : (external = (task_stack_call_external (owned)))) (PreH26 : (platform = (task_stack_call_platform (owned)))) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH29 : ((queue_entries (q_2)) <= 0)) (PreH30 : (0 <= (queue_entries (q_2)))) (PreH31 : ((queue_entries (q_2)) <= 65535)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (q_pend_api_prefix pe before eid )) (PreH34 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH37 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH38 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH44 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH46 : (timeout_pre <= UINT_MAX)) (PreH47 : (0 <= UINT_MAX)) (PreH48 : (timeout_pre >= 0)) (PreH49 : (0 >= 0)) (PreH50 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (pe = (event_addr (sg) (eid)))) (PreH53 : (valid_event_id sg eid )) (PreH54 : (q_query_public_slot before eid observed )) (PreH55 : (UCOS2_state_inv sg before )) (PreH56 : (pevent_pre <> 0)) (PreH57 : (pevent_pre = pe)) (PreH58 : (timeout_pre = ticks)) (PreH59 : (perr_pre = pd)) (PreH60 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH61 : (sem_pend_profile sg )) (PreH62 : (q_accept_profile sg )) (PreH63 : (kernel_tcb_stack_field_layout sg )) (PreH64 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH65 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH66 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH67 : (pe <> 0)) (PreH68 : (event_object_layout_prop sg eid )) (PreH69 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH70 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH71 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH72 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH73 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((node.(statPend) ) = PendTimeout) ” 
  &&  “ (mutex_query_lookup resume_entry eid current ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSQPend_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH12 : (q_pend_sched_admitted environment critical )) (PreH13 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH14 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH15 : (q_pend_wait_entry sg entry eid current_2 tid old )) (PreH16 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH17 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH18 : ((old.(dly) ) <= UINT_MAX)) (PreH19 : (retval <= UINT_MAX)) (PreH20 : (ticks <= UINT_MAX)) (PreH21 : ((old.(dly) ) >= 0)) (PreH22 : (retval >= 0)) (PreH23 : (ticks >= 0)) (PreH24 : (environment = (Some (owned)))) (PreH25 : (external = (task_stack_call_external (owned)))) (PreH26 : (platform = (task_stack_call_platform (owned)))) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old )) (PreH29 : ((queue_entries (q_2)) <= 0)) (PreH30 : (0 <= (queue_entries (q_2)))) (PreH31 : ((queue_entries (q_2)) <= 65535)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (q_pend_api_prefix pe before eid )) (PreH34 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH37 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH38 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH44 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH46 : (timeout_pre <= UINT_MAX)) (PreH47 : (0 <= UINT_MAX)) (PreH48 : (timeout_pre >= 0)) (PreH49 : (0 >= 0)) (PreH50 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (pe = (event_addr (sg) (eid)))) (PreH53 : (valid_event_id sg eid )) (PreH54 : (q_query_public_slot before eid observed )) (PreH55 : (UCOS2_state_inv sg before )) (PreH56 : (pevent_pre <> 0)) (PreH57 : (pevent_pre = pe)) (PreH58 : (timeout_pre = ticks)) (PreH59 : (perr_pre = pd)) (PreH60 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH61 : (sem_pend_profile sg )) (PreH62 : (q_accept_profile sg )) (PreH63 : (kernel_tcb_stack_field_layout sg )) (PreH64 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH65 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH66 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH67 : (pe <> 0)) (PreH68 : (event_object_layout_prop sg eid )) (PreH69 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH70 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH71 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH72 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH73 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
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
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current_2 tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current_2 tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 = (encode_pend_status ((node.(statPend) )))) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_24 := OSQPend_partial_solve_wit_24_pure -> OSQPend_partial_solve_wit_24_aux.

Definition OSQPend_partial_solve_wit_25 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current_2 )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH12 : (q_pend_sched_admitted environment critical )) (PreH13 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH14 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH15 : (q_pend_wait_entry sg entry eid current tid old )) (PreH16 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH17 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH18 : ((old.(dly) ) <= UINT_MAX)) (PreH19 : (retval <= UINT_MAX)) (PreH20 : (ticks <= UINT_MAX)) (PreH21 : ((old.(dly) ) >= 0)) (PreH22 : (retval >= 0)) (PreH23 : (ticks >= 0)) (PreH24 : (environment = (Some (owned)))) (PreH25 : (external = (task_stack_call_external (owned)))) (PreH26 : (platform = (task_stack_call_platform (owned)))) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH29 : ((queue_entries (q)) <= 0)) (PreH30 : (0 <= (queue_entries (q)))) (PreH31 : ((queue_entries (q)) <= 65535)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (q_pend_api_prefix pe before eid )) (PreH34 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH37 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH38 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH44 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH46 : (timeout_pre <= UINT_MAX)) (PreH47 : (0 <= UINT_MAX)) (PreH48 : (timeout_pre >= 0)) (PreH49 : (0 >= 0)) (PreH50 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (pe = (event_addr (sg) (eid)))) (PreH53 : (valid_event_id sg eid )) (PreH54 : (q_query_public_slot before eid observed )) (PreH55 : (UCOS2_state_inv sg before )) (PreH56 : (pevent_pre <> 0)) (PreH57 : (pevent_pre = pe)) (PreH58 : (timeout_pre = ticks)) (PreH59 : (perr_pre = pd)) (PreH60 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH61 : (sem_pend_profile sg )) (PreH62 : (q_accept_profile sg )) (PreH63 : (kernel_tcb_stack_field_layout sg )) (PreH64 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH65 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH66 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH67 : (pe <> 0)) (PreH68 : (event_object_layout_prop sg eid )) (PreH69 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH70 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH71 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH72 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH73 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
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
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 = (encode_pend_status ((node.(statPend) )))) ”
  &&  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current_2.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current_2.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current_2 resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_26 := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current_2 )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH6 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH9 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH12 : (q_pend_sched_admitted environment critical )) (PreH13 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH14 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH15 : (q_pend_wait_entry sg entry eid current tid old )) (PreH16 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH17 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH18 : ((old.(dly) ) <= UINT_MAX)) (PreH19 : (retval <= UINT_MAX)) (PreH20 : (ticks <= UINT_MAX)) (PreH21 : ((old.(dly) ) >= 0)) (PreH22 : (retval >= 0)) (PreH23 : (ticks >= 0)) (PreH24 : (environment = (Some (owned)))) (PreH25 : (external = (task_stack_call_external (owned)))) (PreH26 : (platform = (task_stack_call_platform (owned)))) (PreH27 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH28 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH29 : ((queue_entries (q)) <= 0)) (PreH30 : (0 <= (queue_entries (q)))) (PreH31 : ((queue_entries (q)) <= 65535)) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (q_pend_api_prefix pe before eid )) (PreH34 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH35 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH36 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH37 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH38 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH39 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH42 : (UCOS2_state_inv sg before )) (PreH43 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH44 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH45 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH46 : (timeout_pre <= UINT_MAX)) (PreH47 : (0 <= UINT_MAX)) (PreH48 : (timeout_pre >= 0)) (PreH49 : (0 >= 0)) (PreH50 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH51 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH52 : (pe = (event_addr (sg) (eid)))) (PreH53 : (valid_event_id sg eid )) (PreH54 : (q_query_public_slot before eid observed )) (PreH55 : (UCOS2_state_inv sg before )) (PreH56 : (pevent_pre <> 0)) (PreH57 : (pevent_pre = pe)) (PreH58 : (timeout_pre = ticks)) (PreH59 : (perr_pre = pd)) (PreH60 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH61 : (sem_pend_profile sg )) (PreH62 : (q_accept_profile sg )) (PreH63 : (kernel_tcb_stack_field_layout sg )) (PreH64 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH65 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH66 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH67 : (pe <> 0)) (PreH68 : (event_object_layout_prop sg eid )) (PreH69 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH70 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH71 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH72 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH73 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
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
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 <> (encode_pend_status ((node.(statPend) )))) ”
  &&  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current_2.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current_2.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid current_2 resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_27_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q_2)) <= 0)) (PreH25 : (0 <= (queue_entries (q_2)))) (PreH26 : ((queue_entries (q_2)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH67 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH68 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 0) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 2) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSQPend_partial_solve_wit_27_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q_2)) <= 0)) (PreH25 : (0 <= (queue_entries (q_2)))) (PreH26 : ((queue_entries (q_2)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH67 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH68 : (1 <> (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
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
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 <> (encode_pend_status ((node.(statPend) )))) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_27 := OSQPend_partial_solve_wit_27_pure -> OSQPend_partial_solve_wit_27_aux.

Definition OSQPend_partial_solve_wit_28_pure := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q_2)) <= 0)) (PreH25 : (0 <= (queue_entries (q_2)))) (PreH26 : ((queue_entries (q_2)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH67 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH68 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((( &( "timeout" ) )) # UInt  |-> ticks)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 0) ” 
  &&  “ ((encode_pend_status ((node.(statPend) ))) <> 2) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
.

Definition OSQPend_partial_solve_wit_28_aux := 
forall (perr_pre: Z) (timeout_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (retval: Z) (q_2: QueueFields) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (owned: TaskStackCallEnvironment) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (retval_2: Z) (resume_tid: Z) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (PreH1 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH2 : (interrupt_saved_value mask retval_2 )) (PreH3 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH4 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH7 : (q_pend_sched_admitted environment critical )) (PreH8 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) (PreH9 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH10 : (q_pend_wait_entry sg entry eid current tid old )) (PreH11 : (0 <= (encode_task_status ((old.(stat) ))))) (PreH12 : ((encode_task_status ((old.(stat) ))) <= 255)) (PreH13 : ((old.(dly) ) <= UINT_MAX)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (ticks <= UINT_MAX)) (PreH16 : ((old.(dly) ) >= 0)) (PreH17 : (retval >= 0)) (PreH18 : (ticks >= 0)) (PreH19 : (environment = (Some (owned)))) (PreH20 : (external = (task_stack_call_external (owned)))) (PreH21 : (platform = (task_stack_call_platform (owned)))) (PreH22 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH23 : (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old )) (PreH24 : ((queue_entries (q_2)) <= 0)) (PreH25 : (0 <= (queue_entries (q_2)))) (PreH26 : ((queue_entries (q_2)) <= 65535)) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (q_pend_api_prefix pe before eid )) (PreH29 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH30 : (0 <= ((before.(IntrState) ).(lockNesting) ))) (PreH31 : (((before.(IntrState) ).(lockNesting) ) <= 255)) (PreH32 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH33 : (0 <= ((before.(IntrState) ).(intNesting) ))) (PreH34 : (((before.(IntrState) ).(intNesting) ) <= 255)) (PreH35 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH36 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH39 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH40 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH41 : (timeout_pre <= UINT_MAX)) (PreH42 : (0 <= UINT_MAX)) (PreH43 : (timeout_pre >= 0)) (PreH44 : (0 >= 0)) (PreH45 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH46 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH47 : (pe = (event_addr (sg) (eid)))) (PreH48 : (valid_event_id sg eid )) (PreH49 : (q_query_public_slot before eid observed )) (PreH50 : (UCOS2_state_inv sg before )) (PreH51 : (pevent_pre <> 0)) (PreH52 : (pevent_pre = pe)) (PreH53 : (timeout_pre = ticks)) (PreH54 : (perr_pre = pd)) (PreH55 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH56 : (sem_pend_profile sg )) (PreH57 : (q_accept_profile sg )) (PreH58 : (kernel_tcb_stack_field_layout sg )) (PreH59 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH60 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH61 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH62 : (pe <> 0)) (PreH63 : (event_object_layout_prop sg eid )) (PreH64 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) (PreH65 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH66 : (0 <> (encode_pend_status ((node.(statPend) ))))) (PreH67 : (2 <> (encode_pend_status ((node.(statPend) ))))) (PreH68 : (1 = (encode_pend_status ((node.(statPend) ))))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
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
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ” 
  &&  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ” 
  &&  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (0 <= (encode_task_status ((old.(stat) )))) ” 
  &&  “ ((encode_task_status ((old.(stat) ))) <= 255) ” 
  &&  “ ((old.(dly) ) <= UINT_MAX) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (ticks <= UINT_MAX) ” 
  &&  “ ((old.(dly) ) >= 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (ticks >= 0) ” 
  &&  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask retval pe before entry eid observed current tid old ) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(lockNesting) )) ” 
  &&  “ (((before.(IntrState) ).(lockNesting) ) <= 255) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 0) ” 
  &&  “ (0 <= ((before.(IntrState) ).(intNesting) )) ” 
  &&  “ (((before.(IntrState) ).(intNesting) ) <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (timeout_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (timeout_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
  &&  “ (q_pend_api_admission environment critical sg context pe before eid ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (2 <> (encode_pend_status ((node.(statPend) )))) ” 
  &&  “ (1 = (encode_pend_status ((node.(statPend) )))) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed retval_2 resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQPend_partial_solve_wit_28 := OSQPend_partial_solve_wit_28_pure -> OSQPend_partial_solve_wit_28_aux.

Definition OSQPend_partial_solve_wit_29_pure := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pq: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
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

Definition OSQPend_partial_solve_wit_29_aux := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (PreH1 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH2 : (q_pend_api_prefix pe before eid )) (PreH3 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH4 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
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
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((pd) # UChar  |-> code)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
.

Definition OSQPend_partial_solve_wit_29 := OSQPend_partial_solve_wit_29_pure -> OSQPend_partial_solve_wit_29_aux.

Definition OSQPend_partial_solve_wit_30_pure := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pq: Z) (pevent: Z) (timeout: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> code)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQPend_partial_solve_wit_30_aux := 
forall (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (ticks: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaning: UCOS2_Verify_State) (resume_tid: Z) (node: TaskAbstractState) (code: Z) (pmsg: Z) (cpu_sr: Z) (checkpoint: UCOS2_Verify_State) (PreH1 : (q_pend_resume_result sg eid resume_entry pmsg code checkpoint )) (PreH2 : (q_pend_api_safe external environment critical sg context pe eid ticks mask before X )) (PreH3 : (q_pend_api_prefix pe before eid )) (PreH4 : (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry )) (PreH5 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((pd) # UChar  |-> code)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (q_pend_resume_result sg eid resume_entry pmsg code checkpoint ) ” 
  &&  “ (q_pend_api_safe external environment critical sg context pe eid ticks mask before X ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ” 
  &&  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (q_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((pd) # UChar  |-> code)
.

Definition OSQPend_partial_solve_wit_30 := OSQPend_partial_solve_wit_30_pure -> OSQPend_partial_solve_wit_30_aux.

Definition OSQPend_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") ) ” 
  &&  “ (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed ) ” 
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
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
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

Definition OSQPend_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSQPend_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (q_query_public_slot before eid observed ) ”
.

Definition OSQPend_which_implies_wit_1_split_goal_3 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSQPend_which_implies_wit_1_split_goal_4 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQPend_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH2 : (pe <> 0)) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
|--
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
.

Definition OSQPend_which_implies_wit_2 := 
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

Definition OSQPend_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (event_core_fields_layout_prop sg eid &((pe)  # "os_event" ->ₛ "OSEventType") &((pe)  # "os_event" ->ₛ "OSEventPtr") &((pe)  # "os_event" ->ₛ "OSEventCnt") )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
.

Definition OSQPend_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_pend_api_prefix pe before eid ) ”
  &&  (q_pend_save_input (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  “ (q_pend_api_prefix pe before eid ) ”
  &&  (q_pend_save_input (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
).

Definition OSQPend_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  “ (q_pend_api_prefix pe before eid ) ”
.

Definition OSQPend_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_pend_api_input critical sg (os_sched_call_invocation (context)) pe before eid observed )) (PreH3 : (q_pend_api_admission environment critical sg context pe before eid )) (PreH4 : (pe <> 0)) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 2)) (PreH6 : (((before.(IntrState) ).(intNesting) ) <= 0)) (PreH7 : (((before.(IntrState) ).(lockNesting) ) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (unmap_table_rep sg )
|--
  (q_pend_save_input (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask before )
.

Definition OSQPend_which_implies_wit_4 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_accept_profile sg )) (PreH2 : (valid_event_id sg eid )) (PreH3 : (pevent = (event_addr (sg) (eid)))) ,
  (q_pend_save_output (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask cpu_sr before )
|--
  EX (current: OSEventAbstractState)  (q: QueueFields)  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_accept_profile sg )) (PreH2 : (valid_event_id sg eid )) (PreH3 : (pevent = (event_addr (sg) (eid)))) ,
  (q_pend_save_output (QueuePendAcquirePhase (pe) (eid) (observed)) external platform environment critical saved_local sg context mask cpu_sr before )
|--
  EX (current: OSEventAbstractState)  (q: QueueFields)  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
).

Definition OSQPend_which_implies_wit_5 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_pointer_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
).

Definition OSQPend_which_implies_wit_6 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) (PreH1 : ((queue_entries (q_2)) > 0)) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_accept_qcb_readonly pq q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (q: QueueFields) ,
  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q next free slots pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (((queue_out_addr (q))) # Ptr  |-> message)
  **  (q_accept_head_slot q slots )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) (PreH1 : ((queue_entries (q_2)) > 0)) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  (q_accept_qcb_readonly pq q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (q: QueueFields) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q next free slots pq message )
  **  (q_accept_qcb_readonly pq q )
  **  (((queue_out_addr (q))) # Ptr  |-> message)
  **  (q_accept_head_slot q slots )
).

Definition OSQPend_which_implies_wit_7 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (message: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (next_2: QueueFields) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q_2 next_2 free_2 slots_2 pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_2)) + 4 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_accept_qcb_readonly pq q_2 )
  **  (((queue_out_addr (q_2))) # Ptr  |-> message)
  **  (q_accept_head_slot q_2 slots_2 )
|--
  EX (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (q: QueueFields)  (message_2: Z) ,
  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q next free slots pq message_2 )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (message: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (next_2: QueueFields) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q_2 next_2 free_2 slots_2 pq message )
  **  (q_accept_qcb_readonly pq q_2 )
  **  (((queue_out_addr (q_2))) # Ptr  |-> message)
  **  (q_accept_head_slot q_2 slots_2 )
|--
  EX (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (q: QueueFields) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ (((queue_out_addr (q_2)) + 4 ) = ((queue_out_addr (q)) + 4 )) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_pend_first_owner external platform environment critical saved_local sg context entered mask cpu_sr pe before entry eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry eid observed current q next free slots pq message )
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
).

Definition OSQPend_which_implies_wit_8 := 
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (message: Z) (slots: (@list (@option Z))) (free: (@list Z)) (next: QueueFields) (q: QueueFields) (current: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current q next free slots pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint ) ”
  &&  (q_pend_restore_input None external platform environment critical saved_local sg entered mask cpu_sr entry checkpoint )
) \/
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (message: Z) (slots: (@list (@option Z))) (free: (@list Z)) (next: QueueFields) (q: QueueFields) (current: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_dequeue_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current q next free slots pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (q_pend_immediate_checkpoint external environment critical sg context before entered entry eid ticks message checkpoint ) ”
  &&  (q_pend_restore_input None external platform environment critical saved_local sg entered mask cpu_sr entry checkpoint )
).

Definition OSQPend_which_implies_wit_9 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState)  (owned: TaskStackCallEnvironment) ,
  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old ) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (entered_2: OsSchedCallContext) (cpu_sr: Z) (pq: Z) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (event_object_layout_prop sg eid )) (PreH3 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_first_owner external platform environment critical saved_local sg context entered_2 mask cpu_sr pe before entry_2 eid observed )
  **  (q_accept_store_context platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask cpu_sr before entry_2 eid observed current_2 q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entered: OsSchedCallContext)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState)  (owned: TaskStackCallEnvironment) ,
  “ (environment = (Some (owned))) ” 
  &&  “ (external = (task_stack_call_external (owned))) ” 
  &&  “ (platform = (task_stack_call_platform (owned))) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ” 
  &&  “ (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old ) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((old.(stat) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((old.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (old.(dly) ))
  **  (sem_pend_prefix_frame sg entry tid old )
).

Definition OSQPend_which_implies_wit_10 := 
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH3 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  “ (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old ) ” 
  &&  “ (q_pend_wait_entry sg entry eid current tid old ) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_pend_wait_call_pre sg entry eid current tid old ticks )
) \/
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (ticks <= UINT_MAX)) (PreH2 : (ticks >= 0)) (PreH3 : (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  “ (q_pend_wait_entry sg entry eid current tid old ) ”
  &&  (q_pend_wait_call_pre sg entry eid current tid old ticks )
).

Definition OSQPend_which_implies_wit_10_split_goal_1 := 
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (ticks <= UINT_MAX)) (PreH2 : (ticks >= 0)) (PreH3 : (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  “ (q_pend_wait_entry sg entry eid current tid old ) ”
.

Definition OSQPend_which_implies_wit_10_split_goal_spatial := 
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (pevent: Z) (PreH1 : (ticks <= UINT_MAX)) (PreH2 : (ticks >= 0)) (PreH3 : (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH4 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) (PreH5 : (pevent = (event_addr (sg) (eid)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((old.(stat) ))) 4))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg entry tid old )
|--
  (q_pend_wait_call_pre sg entry eid current tid old ticks )
.

Definition OSQPend_which_implies_wit_11 := 
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH2 : (kernel_tcb_stack_field_layout sg )) ,
  (q_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  (q_pend_wait_call_post sg entry eid current tid old ticks )
|--
  EX (waiting: UCOS2_Verify_State) ,
  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ”
  &&  (q_pend_restore_input (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask cpu_sr entry waiting )
) \/
(
forall (ticks: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (q_pend_empty_snapshot external environment critical sg context entered mask cpu_sr pe before entry eid observed current tid old )) (PreH2 : (kernel_tcb_stack_field_layout sg )) ,
  (q_pend_masked_frame external platform environment critical saved_local sg entered cpu_sr entry entry )
  **  (q_pend_wait_call_post sg entry eid current tid old ticks )
|--
  EX (waiting: UCOS2_Verify_State) ,
  “ (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting ) ”
  &&  (q_pend_restore_input (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask cpu_sr entry waiting )
).

Definition OSQPend_which_implies_wit_12 := 
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) ,
  (q_pend_restore_output (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask waiting )
|--
  EX (released: OsSchedCallContext)  (unmasked: UCOS2_Verify_State) ,
  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ”
  &&  (q_pend_continuation_phase_sched_input (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
) \/
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (entered: OsSchedCallContext) (PreH1 : (q_pend_first_wait_checkpoint external environment critical sg context before entered entry eid ticks waiting )) ,
  (q_pend_restore_output (Some ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg entered mask waiting )
|--
  EX (released: OsSchedCallContext)  (unmasked: UCOS2_Verify_State) ,
  “ (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked ) ” 
  &&  “ (q_pend_sched_admitted environment critical ) ”
  &&  (q_pend_continuation_phase_sched_input (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
).

Definition OSQPend_which_implies_wit_13 := 
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (unmasked: UCOS2_Verify_State) (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (released: OsSchedCallContext) (PreH1 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH2 : (q_pend_sched_admitted environment critical )) ,
  (q_pend_continuation_phase_sched_output (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
|--
  EX (scheduled: OsSchedCallContext)  (selected: UCOS2_Verify_State) ,
  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ”
  &&  (q_pend_save_input (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg scheduled mask selected )
) \/
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (unmasked: UCOS2_Verify_State) (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (released: OsSchedCallContext) (PreH1 : (q_pend_scheduling_checkpoint external environment critical sg context before entry eid ticks waiting released unmasked )) (PreH2 : (q_pend_sched_admitted environment critical )) ,
  (q_pend_continuation_phase_sched_output (QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)) external platform environment critical saved_local sg released mask unmasked )
|--
  EX (scheduled: OsSchedCallContext)  (selected: UCOS2_Verify_State) ,
  “ (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected ) ”
  &&  (q_pend_save_input (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg scheduled mask selected )
).

Definition OSQPend_which_implies_wit_14 := 
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (scheduled: OsSchedCallContext) (current: OSEventAbstractState) (selected: UCOS2_Verify_State) (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_save_output (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg scheduled mask cpu_sr selected )
|--
  EX (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
) \/
(
forall (ticks: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (scheduled: OsSchedCallContext) (current: OSEventAbstractState) (selected: UCOS2_Verify_State) (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (q_pend_scheduled_checkpoint external environment critical sg context before eid ticks scheduled selected )) (PreH2 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_save_output (QueuePendResumePhase ((QueuePendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) (waiting)))) external platform environment critical saved_local sg scheduled mask cpu_sr selected )
|--
  EX (resume_tid: Z)  (node: TaskAbstractState)  (resumed: OsSchedCallContext)  (resume_entry: UCOS2_Verify_State) ,
  “ (q_pend_resume_checkpoint external environment critical sg context before eid ticks resumed resume_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (sem_pend_resume_entry sg resume_entry eid resume_tid node ) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((node.(msg) ))))
  **  (q_pend_cleanup_frame sg resume_entry resume_tid node )
).

Definition OSQPend_which_implies_wit_15 := 
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
|--
  EX (cleaning: UCOS2_Verify_State)  (cleaned_node: TaskAbstractState) ,
  “ (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
) \/
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current: OSEventAbstractState) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((node.(statPend) ) = PendTimeout)) (PreH3 : (mutex_query_lookup resume_entry eid current )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
|--
  EX (cleaning: UCOS2_Verify_State)  (cleaned_node: TaskAbstractState) ,
  “ (q_pend_cleanup_observation sg resume_entry eid 0 10 cleaning resume_tid cleaned_node ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) )) ”
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((cleaned_node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((cleaned_node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((cleaned_node.(eventPtr) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((cleaned_node.(msg) ))))
  **  (q_pend_cleanup_frame sg cleaning resume_tid cleaned_node )
).

Definition OSQPend_which_implies_wit_16 := 
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((encode_pend_status ((node.(statPend) ))) <> 0)) (PreH3 : ((encode_pend_status ((node.(statPend) ))) <> 2)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
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
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
) \/
(
forall (eid: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (node: TaskAbstractState) (resume_tid: Z) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (sem_pend_resume_entry sg resume_entry eid resume_tid node )) (PreH2 : ((encode_pend_status ((node.(statPend) ))) <> 0)) (PreH3 : ((encode_pend_status ((node.(statPend) ))) <> 2)) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
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
  &&  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry resume_entry )
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid current resume_tid node )
).

Definition OSQPend_which_implies_wit_17 := 
(
forall (eid: Z) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (code: Z) (node: TaskAbstractState) (resume_tid: Z) (cleaning: UCOS2_Verify_State) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (pmsg: Z) (cpu_sr: Z) (perr: Z) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
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
  &&  (q_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
  **  ((perr) # UChar  |-> code)
) \/
(
forall (eid: Z) (mask: Z) (saved_local: (Armv7aContinuation -> Assertion)) (environment: (@option TaskStackCallEnvironment)) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (code: Z) (node: TaskAbstractState) (resume_tid: Z) (cleaning: UCOS2_Verify_State) (resume_entry: UCOS2_Verify_State) (resumed: OsSchedCallContext) (pmsg: Z) (cpu_sr: Z) (PreH1 : (q_pend_cleanup_observation sg resume_entry eid pmsg code cleaning resume_tid node )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (( &( "OSTCBCur" ) ) = (sg.(g_OSTCBCur) ))) ,
  (q_pend_masked_frame external platform environment critical saved_local sg resumed cpu_sr resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  (q_pend_cleanup_frame sg cleaning resume_tid node )
|--
  EX (checkpoint: UCOS2_Verify_State) ,
  “ (q_pend_resume_result sg eid resume_entry pmsg code checkpoint ) ”
  &&  (q_pend_restore_input None external platform environment critical saved_local sg resumed mask cpu_sr resume_entry checkpoint )
).

Module Type VC_Correct.


Axiom proof_of_OSQPend_safety_wit_1 : OSQPend_safety_wit_1.
Axiom proof_of_OSQPend_safety_wit_2 : OSQPend_safety_wit_2.
Axiom proof_of_OSQPend_safety_wit_3 : OSQPend_safety_wit_3.
Axiom proof_of_OSQPend_safety_wit_4 : OSQPend_safety_wit_4.
Axiom proof_of_OSQPend_safety_wit_5 : OSQPend_safety_wit_5.
Axiom proof_of_OSQPend_safety_wit_6 : OSQPend_safety_wit_6.
Axiom proof_of_OSQPend_safety_wit_7 : OSQPend_safety_wit_7.
Axiom proof_of_OSQPend_safety_wit_8 : OSQPend_safety_wit_8.
Axiom proof_of_OSQPend_safety_wit_9 : OSQPend_safety_wit_9.
Axiom proof_of_OSQPend_safety_wit_10 : OSQPend_safety_wit_10.
Axiom proof_of_OSQPend_safety_wit_11 : OSQPend_safety_wit_11.
Axiom proof_of_OSQPend_safety_wit_12 : OSQPend_safety_wit_12.
Axiom proof_of_OSQPend_safety_wit_13 : OSQPend_safety_wit_13.
Axiom proof_of_OSQPend_safety_wit_14 : OSQPend_safety_wit_14.
Axiom proof_of_OSQPend_safety_wit_15 : OSQPend_safety_wit_15.
Axiom proof_of_OSQPend_safety_wit_16 : OSQPend_safety_wit_16.
Axiom proof_of_OSQPend_safety_wit_17 : OSQPend_safety_wit_17.
Axiom proof_of_OSQPend_safety_wit_18 : OSQPend_safety_wit_18.
Axiom proof_of_OSQPend_safety_wit_19 : OSQPend_safety_wit_19.
Axiom proof_of_OSQPend_entail_wit_1 : OSQPend_entail_wit_1.
Axiom proof_of_OSQPend_entail_wit_2 : OSQPend_entail_wit_2.
Axiom proof_of_OSQPend_entail_wit_3 : OSQPend_entail_wit_3.
Axiom proof_of_OSQPend_entail_wit_4 : OSQPend_entail_wit_4.
Axiom proof_of_OSQPend_entail_wit_5_1 : OSQPend_entail_wit_5_1.
Axiom proof_of_OSQPend_entail_wit_5_2 : OSQPend_entail_wit_5_2.
Axiom proof_of_OSQPend_entail_wit_5_3 : OSQPend_entail_wit_5_3.
Axiom proof_of_OSQPend_entail_wit_5_4 : OSQPend_entail_wit_5_4.
Axiom proof_of_OSQPend_return_wit_1 : OSQPend_return_wit_1.
Axiom proof_of_OSQPend_return_wit_2 : OSQPend_return_wit_2.
Axiom proof_of_OSQPend_return_wit_3 : OSQPend_return_wit_3.
Axiom proof_of_OSQPend_return_wit_4 : OSQPend_return_wit_4.
Axiom proof_of_OSQPend_return_wit_5 : OSQPend_return_wit_5.
Axiom proof_of_OSQPend_return_wit_6 : OSQPend_return_wit_6.
Axiom proof_of_OSQPend_return_wit_7 : OSQPend_return_wit_7.
Axiom proof_of_OSQPend_partial_solve_wit_1_pure : OSQPend_partial_solve_wit_1_pure.
Axiom proof_of_OSQPend_partial_solve_wit_1 : OSQPend_partial_solve_wit_1.
Axiom proof_of_OSQPend_partial_solve_wit_2_pure : OSQPend_partial_solve_wit_2_pure.
Axiom proof_of_OSQPend_partial_solve_wit_2 : OSQPend_partial_solve_wit_2.
Axiom proof_of_OSQPend_partial_solve_wit_3_pure : OSQPend_partial_solve_wit_3_pure.
Axiom proof_of_OSQPend_partial_solve_wit_3 : OSQPend_partial_solve_wit_3.
Axiom proof_of_OSQPend_partial_solve_wit_4 : OSQPend_partial_solve_wit_4.
Axiom proof_of_OSQPend_partial_solve_wit_5_pure : OSQPend_partial_solve_wit_5_pure.
Axiom proof_of_OSQPend_partial_solve_wit_5 : OSQPend_partial_solve_wit_5.
Axiom proof_of_OSQPend_partial_solve_wit_6_pure : OSQPend_partial_solve_wit_6_pure.
Axiom proof_of_OSQPend_partial_solve_wit_6 : OSQPend_partial_solve_wit_6.
Axiom proof_of_OSQPend_partial_solve_wit_7_pure : OSQPend_partial_solve_wit_7_pure.
Axiom proof_of_OSQPend_partial_solve_wit_7 : OSQPend_partial_solve_wit_7.
Axiom proof_of_OSQPend_partial_solve_wit_8 : OSQPend_partial_solve_wit_8.
Axiom proof_of_OSQPend_partial_solve_wit_9_pure : OSQPend_partial_solve_wit_9_pure.
Axiom proof_of_OSQPend_partial_solve_wit_9 : OSQPend_partial_solve_wit_9.
Axiom proof_of_OSQPend_partial_solve_wit_10_pure : OSQPend_partial_solve_wit_10_pure.
Axiom proof_of_OSQPend_partial_solve_wit_10 : OSQPend_partial_solve_wit_10.
Axiom proof_of_OSQPend_partial_solve_wit_11_pure : OSQPend_partial_solve_wit_11_pure.
Axiom proof_of_OSQPend_partial_solve_wit_11 : OSQPend_partial_solve_wit_11.
Axiom proof_of_OSQPend_partial_solve_wit_12_pure : OSQPend_partial_solve_wit_12_pure.
Axiom proof_of_OSQPend_partial_solve_wit_12 : OSQPend_partial_solve_wit_12.
Axiom proof_of_OSQPend_partial_solve_wit_13_pure : OSQPend_partial_solve_wit_13_pure.
Axiom proof_of_OSQPend_partial_solve_wit_13 : OSQPend_partial_solve_wit_13.
Axiom proof_of_OSQPend_partial_solve_wit_14_pure : OSQPend_partial_solve_wit_14_pure.
Axiom proof_of_OSQPend_partial_solve_wit_14 : OSQPend_partial_solve_wit_14.
Axiom proof_of_OSQPend_partial_solve_wit_15_pure : OSQPend_partial_solve_wit_15_pure.
Axiom proof_of_OSQPend_partial_solve_wit_15 : OSQPend_partial_solve_wit_15.
Axiom proof_of_OSQPend_partial_solve_wit_16_pure : OSQPend_partial_solve_wit_16_pure.
Axiom proof_of_OSQPend_partial_solve_wit_16 : OSQPend_partial_solve_wit_16.
Axiom proof_of_OSQPend_partial_solve_wit_17_pure : OSQPend_partial_solve_wit_17_pure.
Axiom proof_of_OSQPend_partial_solve_wit_17 : OSQPend_partial_solve_wit_17.
Axiom proof_of_OSQPend_partial_solve_wit_18_pure : OSQPend_partial_solve_wit_18_pure.
Axiom proof_of_OSQPend_partial_solve_wit_18 : OSQPend_partial_solve_wit_18.
Axiom proof_of_OSQPend_partial_solve_wit_19_pure : OSQPend_partial_solve_wit_19_pure.
Axiom proof_of_OSQPend_partial_solve_wit_19 : OSQPend_partial_solve_wit_19.
Axiom proof_of_OSQPend_partial_solve_wit_20_pure : OSQPend_partial_solve_wit_20_pure.
Axiom proof_of_OSQPend_partial_solve_wit_20 : OSQPend_partial_solve_wit_20.
Axiom proof_of_OSQPend_partial_solve_wit_21 : OSQPend_partial_solve_wit_21.
Axiom proof_of_OSQPend_partial_solve_wit_22_pure : OSQPend_partial_solve_wit_22_pure.
Axiom proof_of_OSQPend_partial_solve_wit_22 : OSQPend_partial_solve_wit_22.
Axiom proof_of_OSQPend_partial_solve_wit_23_pure : OSQPend_partial_solve_wit_23_pure.
Axiom proof_of_OSQPend_partial_solve_wit_23 : OSQPend_partial_solve_wit_23.
Axiom proof_of_OSQPend_partial_solve_wit_24_pure : OSQPend_partial_solve_wit_24_pure.
Axiom proof_of_OSQPend_partial_solve_wit_24 : OSQPend_partial_solve_wit_24.
Axiom proof_of_OSQPend_partial_solve_wit_25 : OSQPend_partial_solve_wit_25.
Axiom proof_of_OSQPend_partial_solve_wit_26 : OSQPend_partial_solve_wit_26.
Axiom proof_of_OSQPend_partial_solve_wit_27_pure : OSQPend_partial_solve_wit_27_pure.
Axiom proof_of_OSQPend_partial_solve_wit_27 : OSQPend_partial_solve_wit_27.
Axiom proof_of_OSQPend_partial_solve_wit_28_pure : OSQPend_partial_solve_wit_28_pure.
Axiom proof_of_OSQPend_partial_solve_wit_28 : OSQPend_partial_solve_wit_28.
Axiom proof_of_OSQPend_partial_solve_wit_29_pure : OSQPend_partial_solve_wit_29_pure.
Axiom proof_of_OSQPend_partial_solve_wit_29 : OSQPend_partial_solve_wit_29.
Axiom proof_of_OSQPend_partial_solve_wit_30_pure : OSQPend_partial_solve_wit_30_pure.
Axiom proof_of_OSQPend_partial_solve_wit_30 : OSQPend_partial_solve_wit_30.
Axiom proof_of_OSQPend_which_implies_wit_1 : OSQPend_which_implies_wit_1.
Axiom proof_of_OSQPend_which_implies_wit_2 : OSQPend_which_implies_wit_2.
Axiom proof_of_OSQPend_which_implies_wit_3 : OSQPend_which_implies_wit_3.
Axiom proof_of_OSQPend_which_implies_wit_4 : OSQPend_which_implies_wit_4.
Axiom proof_of_OSQPend_which_implies_wit_5 : OSQPend_which_implies_wit_5.
Axiom proof_of_OSQPend_which_implies_wit_6 : OSQPend_which_implies_wit_6.
Axiom proof_of_OSQPend_which_implies_wit_7 : OSQPend_which_implies_wit_7.
Axiom proof_of_OSQPend_which_implies_wit_8 : OSQPend_which_implies_wit_8.
Axiom proof_of_OSQPend_which_implies_wit_9 : OSQPend_which_implies_wit_9.
Axiom proof_of_OSQPend_which_implies_wit_10 : OSQPend_which_implies_wit_10.
Axiom proof_of_OSQPend_which_implies_wit_11 : OSQPend_which_implies_wit_11.
Axiom proof_of_OSQPend_which_implies_wit_12 : OSQPend_which_implies_wit_12.
Axiom proof_of_OSQPend_which_implies_wit_13 : OSQPend_which_implies_wit_13.
Axiom proof_of_OSQPend_which_implies_wit_14 : OSQPend_which_implies_wit_14.
Axiom proof_of_OSQPend_which_implies_wit_15 : OSQPend_which_implies_wit_15.
Axiom proof_of_OSQPend_which_implies_wit_16 : OSQPend_which_implies_wit_16.
Axiom proof_of_OSQPend_which_implies_wit_17 : OSQPend_which_implies_wit_17.

End VC_Correct.
