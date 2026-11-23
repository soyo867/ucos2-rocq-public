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
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_source_api_spec.
Local Open Scope sac.

(*----- Function OSSemQuery -----*)

Definition OSSemQuery_safety_wit_1 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_sem_data_pre = pd)) (PreH3 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_sem_data_pre <> 0)) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_2 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_sem_data_pre = pd)) (PreH3 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_sem_data_pre <> 0)) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_3 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_sem_data_pre = pd)) (PreH3 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_sem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_4 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_sem_data_pre = pd)) (PreH3 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_5 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_sem_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_6 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_sem_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_7 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_sem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_8 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_9 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_sem_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_10 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_sem_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_11 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_sem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_12 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_13 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_14 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_15 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_16 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSSemQuery_safety_wit_17 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_sem_data_pre = pd)) (PreH15 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_sem_data_pre <> 0)) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_18 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_sem_data_pre = pd)) (PreH18 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_19 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_sem_data_pre = pd)) (PreH18 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_safety_wit_20 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH13 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH19 : (p_sem_data_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (p_sem_data_pre = pd)) (PreH23 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_sem_data_pre <> 0)) (PreH26 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OSSemQuery_safety_wit_21 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (i >= 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (p_sem_data_pre <> 0)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (p_sem_data_pre = pd)) (PreH26 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_sem_data_pre <> 0)) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (sem_query_output_fields pd cnt grp )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemQuery_entail_wit_1_1 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (p_sem_data_pre <> 0)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (p_sem_data_pre = pd)) (PreH7 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_sem_data_pre <> 0)) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_entail_wit_1_2 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (p_sem_data_pre <> 0)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (p_sem_data_pre = pd)) (PreH7 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_sem_data_pre <> 0)) (PreH10 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_sem_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_sem_data_pre = pd)) (PreH9 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ”
  &&  emp
).

Definition OSSemQuery_entail_wit_1_2_split_goal_1 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_sem_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_sem_data_pre = pd)) (PreH9 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)
.

Definition OSSemQuery_entail_wit_1_2_split_goal_2 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_sem_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_sem_data_pre = pd)) (PreH9 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))
.

Definition OSSemQuery_entail_wit_2 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cnt_2: Z) (grp_2: Z) (evtL_2: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_sem_data_pre = pd)) (PreH18 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 0 )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL 0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cnt_2: Z) (grp_2: Z) (evtL_2: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_sem_data_pre = pd)) (PreH18 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 0 )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL 0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSSemQuery_entail_wit_3 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (pdest_v_2: Z) (psrc_v_2: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cnt_2: Z) (grp_2: Z) (evtL_2: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest_v_2 = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (i < 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH19 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH20 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_sem_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_sem_data_pre = pd)) (PreH30 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_sem_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 (i + 1 ) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((psrc_v + 1 ) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((pdest_v + 1 ) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL (i + 1 ) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (pdest_v_2: Z) (psrc_v_2: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (cnt_2: Z) (grp_2: Z) (evtL_2: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest_v_2 = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (i < 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH19 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH20 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_sem_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_sem_data_pre = pd)) (PreH30 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_sem_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 (i + 1 ) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((psrc_v + 1 ) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((pdest_v + 1 ) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL (i + 1 ) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSSemQuery_return_wit_1 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (i >= 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (p_sem_data_pre <> 0)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (p_sem_data_pre = pd)) (PreH26 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_sem_data_pre <> 0)) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (i >= 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (p_sem_data_pre <> 0)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (p_sem_data_pre = pd)) (PreH26 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_sem_data_pre <> 0)) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
).

Definition OSSemQuery_return_wit_1_split_goal_spatial := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation entry after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (i >= 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH17 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (p_sem_data_pre <> 0)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (p_sem_data_pre = pd)) (PreH26 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_sem_data_pre <> 0)) (PreH29 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
.

Definition OSSemQuery_return_wit_2 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
).

Definition OSSemQuery_return_wit_2_split_goal_spatial := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
.

Definition OSSemQuery_return_wit_3 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre = 0)) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre = 0)) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
).

Definition OSSemQuery_return_wit_3_split_goal_spatial := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre = 0)) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
.

Definition OSSemQuery_return_wit_4 := 
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
) \/
(
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
).

Definition OSSemQuery_return_wit_4_split_goal_spatial := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_sem_data_pre = pd)) (PreH4 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_query_source_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
.

Definition OSSemQuery_partial_solve_wit_1_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSSemQuery_partial_solve_wit_1_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <> 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSSemQuery_partial_solve_wit_1 := OSSemQuery_partial_solve_wit_1_pure -> OSSemQuery_partial_solve_wit_1_aux.

Definition OSSemQuery_partial_solve_wit_2_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSSemQuery_partial_solve_wit_2_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_sem_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_sem_data_pre = pd)) (PreH5 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_sem_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> p_sem_data_pre)
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_partial_solve_wit_2 := OSSemQuery_partial_solve_wit_2_pure -> OSSemQuery_partial_solve_wit_2_aux.

Definition OSSemQuery_partial_solve_wit_3_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSSemQuery_partial_solve_wit_3_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_sem_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_sem_data_pre = pd)) (PreH12 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_partial_solve_wit_3 := OSSemQuery_partial_solve_wit_3_pure -> OSSemQuery_partial_solve_wit_3_aux.

Definition OSSemQuery_partial_solve_wit_4_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_sem_data_pre = pd)) (PreH15 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_sem_data_pre <> 0)) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
.

Definition OSSemQuery_partial_solve_wit_4_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_sem_data_pre = pd)) (PreH15 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_sem_data_pre <> 0)) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_partial_solve_wit_4 := OSSemQuery_partial_solve_wit_4_pure -> OSSemQuery_partial_solve_wit_4_aux.

Definition OSSemQuery_partial_solve_wit_5_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_sem_data_pre = pd)) (PreH15 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_sem_data_pre <> 0)) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemQuery_partial_solve_wit_5_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH4 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH5 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : (p_sem_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_sem_data_pre = pd)) (PreH15 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_sem_data_pre <> 0)) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_partial_solve_wit_5 := OSSemQuery_partial_solve_wit_5_pure -> OSSemQuery_partial_solve_wit_5_aux.

Definition OSSemQuery_partial_solve_wit_6_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH6 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : (p_sem_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (p_sem_data_pre = pd)) (PreH16 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (p_sem_data_pre <> 0)) (PreH19 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemQuery_partial_solve_wit_6_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH6 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : (p_sem_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (p_sem_data_pre = pd)) (PreH16 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (p_sem_data_pre <> 0)) (PreH19 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_partial_solve_wit_6 := OSSemQuery_partial_solve_wit_6_pure -> OSSemQuery_partial_solve_wit_6_aux.

Definition OSSemQuery_partial_solve_wit_7_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH7 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : (p_sem_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (p_sem_data_pre = pd)) (PreH17 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (p_sem_data_pre <> 0)) (PreH20 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemQuery_partial_solve_wit_7_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH6 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH7 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH8 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : (p_sem_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (p_sem_data_pre = pd)) (PreH17 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (p_sem_data_pre <> 0)) (PreH20 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSSemQuery_partial_solve_wit_7 := OSSemQuery_partial_solve_wit_7_pure -> OSSemQuery_partial_solve_wit_7_aux.

Definition OSSemQuery_partial_solve_wit_8 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH7 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH8 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH9 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH14 : (p_sem_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_sem_data_pre = pd)) (PreH18 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (sem_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemQuery_partial_solve_wit_9_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_sem_data_pre = pd)) (PreH24 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_sem_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSSemQuery_partial_solve_wit_9_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_sem_data_pre = pd)) (PreH24 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_sem_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemQuery_partial_solve_wit_9 := OSSemQuery_partial_solve_wit_9_pure -> OSSemQuery_partial_solve_wit_9_aux.

Definition OSSemQuery_partial_solve_wit_10_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH17 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH23 : (p_sem_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (p_sem_data_pre = pd)) (PreH27 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_sem_data_pre <> 0)) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSSemQuery_partial_solve_wit_10_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH17 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH18 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH23 : (p_sem_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (p_sem_data_pre = pd)) (PreH27 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_sem_data_pre <> 0)) (PreH30 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  (((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemQuery_partial_solve_wit_10 := OSSemQuery_partial_solve_wit_10_pure -> OSSemQuery_partial_solve_wit_10_aux.

Definition OSSemQuery_partial_solve_wit_11_pure := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_sem_data_pre = pd)) (PreH24 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_sem_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_sem_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |-> cnt)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemQuery_partial_solve_wit_11_aux := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH14 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH15 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_sem_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_sem_data_pre = pd)) (PreH24 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_sem_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |-> cnt)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |-> cnt)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemQuery_partial_solve_wit_11 := OSSemQuery_partial_solve_wit_11_pure -> OSSemQuery_partial_solve_wit_11_aux.

Definition OSSemQuery_partial_solve_wit_12 := 
forall (p_sem_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option SemQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH14 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH15 : (0 <= (event_slot_type_value ((before.(EventState) )) (eid)))) (PreH16 : ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH21 : (p_sem_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (p_sem_data_pre = pd)) (PreH25 : (sem_query_source_api_safe critical sg invocation eid pe pd before X )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (p_sem_data_pre <> 0)) (PreH28 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((before.(EventState) )) (eid))) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_sem_data_pre = pd) ” 
  &&  “ (sem_query_source_api_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_sem_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((before.(EventState) )) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (sem_query_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemQuery_which_implies_wit_1 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
).

Definition OSSemQuery_which_implies_wit_1_split_goal_1 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemQuery_which_implies_wit_1_split_goal_spatial := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
.

Definition OSSemQuery_which_implies_wit_2 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_inv sg before )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_inv sg before )
).

Definition OSSemQuery_which_implies_wit_2_split_goal_1 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemQuery_which_implies_wit_2_split_goal_2 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
.

Definition OSSemQuery_which_implies_wit_2_split_goal_spatial := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((before.(EventState) )) (eid)) = 3)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_inv sg before )
.

Definition OSSemQuery_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
).

Definition OSSemQuery_which_implies_wit_4 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  (used_event_rest_no_type_cnt_ptr sg (entry_2.(TskState) ) pe eid current_2 )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  (used_event_rest_no_type_cnt_ptr sg (entry_2.(TskState) ) pe eid current_2 )
|--
  EX (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
).

Definition OSSemQuery_which_implies_wit_5 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_oseventtbl sg pe evtL_2 )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 3)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_oseventtbl sg pe evtL_2 )
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
).

Definition OSSemQuery_which_implies_wit_6 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) ,
  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL_2 )
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL 0 )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) ,
  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (UCharArray.undef_full &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") 8 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (grp: Z)  (evtL: (@list Z)) ,
  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL 0 )
).

Definition OSSemQuery_which_implies_wit_7 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v: Z) (psrc_v: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |->_)
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v: Z) (psrc_v: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 i )
|--
  EX (x: Z)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  ((pdest_v) # UChar  |-> x)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
).

Definition OSSemQuery_which_implies_wit_8 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v_2: Z) (psrc_v_2: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v_2 = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v_2 + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v_2 + 1 ))
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  ((psrc_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL_2 i )
  **  ((pdest_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (pdest_v: Z)  (psrc_v: Z) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + 1 ))
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |->_)
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL (i + 1 ) )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v_2: Z) (psrc_v_2: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v_2 = (&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((psrc_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL_2 i )
  **  ((pdest_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (sem_query_output_table_missing_i &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (grp: Z)  (evtL: (@list Z)) ,
  “ ((pdest_v_2 + 1 ) = ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ ((psrc_v_2 + 1 ) = ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ ((pdest_v_2 + 1 ) = ((&((pd)  # "os_sem_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ ((psrc_v_2 + 1 ) = ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL (i + 1 ) )
).

Definition OSSemQuery_which_implies_wit_9 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |-> cnt_2)
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 i )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pd)  # "os_sem_data" ->ₛ "OSCnt")) # UShort  |-> cnt_2)
  **  (store_oseventtbl sg pe evtL_2 )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL_2 i )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (sem_query_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry )
  **  (sem_query_output_fields pd cnt grp )
  **  (sem_query_output_table &((pd)  # "os_sem_data" ->ₛ "OSEventTbl") evtL i )
).

Module Type VC_Correct.


Axiom proof_of_OSSemQuery_safety_wit_1 : OSSemQuery_safety_wit_1.
Axiom proof_of_OSSemQuery_safety_wit_2 : OSSemQuery_safety_wit_2.
Axiom proof_of_OSSemQuery_safety_wit_3 : OSSemQuery_safety_wit_3.
Axiom proof_of_OSSemQuery_safety_wit_4 : OSSemQuery_safety_wit_4.
Axiom proof_of_OSSemQuery_safety_wit_5 : OSSemQuery_safety_wit_5.
Axiom proof_of_OSSemQuery_safety_wit_6 : OSSemQuery_safety_wit_6.
Axiom proof_of_OSSemQuery_safety_wit_7 : OSSemQuery_safety_wit_7.
Axiom proof_of_OSSemQuery_safety_wit_8 : OSSemQuery_safety_wit_8.
Axiom proof_of_OSSemQuery_safety_wit_9 : OSSemQuery_safety_wit_9.
Axiom proof_of_OSSemQuery_safety_wit_10 : OSSemQuery_safety_wit_10.
Axiom proof_of_OSSemQuery_safety_wit_11 : OSSemQuery_safety_wit_11.
Axiom proof_of_OSSemQuery_safety_wit_12 : OSSemQuery_safety_wit_12.
Axiom proof_of_OSSemQuery_safety_wit_13 : OSSemQuery_safety_wit_13.
Axiom proof_of_OSSemQuery_safety_wit_14 : OSSemQuery_safety_wit_14.
Axiom proof_of_OSSemQuery_safety_wit_15 : OSSemQuery_safety_wit_15.
Axiom proof_of_OSSemQuery_safety_wit_16 : OSSemQuery_safety_wit_16.
Axiom proof_of_OSSemQuery_safety_wit_17 : OSSemQuery_safety_wit_17.
Axiom proof_of_OSSemQuery_safety_wit_18 : OSSemQuery_safety_wit_18.
Axiom proof_of_OSSemQuery_safety_wit_19 : OSSemQuery_safety_wit_19.
Axiom proof_of_OSSemQuery_safety_wit_20 : OSSemQuery_safety_wit_20.
Axiom proof_of_OSSemQuery_safety_wit_21 : OSSemQuery_safety_wit_21.
Axiom proof_of_OSSemQuery_entail_wit_1_1 : OSSemQuery_entail_wit_1_1.
Axiom proof_of_OSSemQuery_entail_wit_1_2 : OSSemQuery_entail_wit_1_2.
Axiom proof_of_OSSemQuery_entail_wit_2 : OSSemQuery_entail_wit_2.
Axiom proof_of_OSSemQuery_entail_wit_3 : OSSemQuery_entail_wit_3.
Axiom proof_of_OSSemQuery_return_wit_1 : OSSemQuery_return_wit_1.
Axiom proof_of_OSSemQuery_return_wit_2 : OSSemQuery_return_wit_2.
Axiom proof_of_OSSemQuery_return_wit_3 : OSSemQuery_return_wit_3.
Axiom proof_of_OSSemQuery_return_wit_4 : OSSemQuery_return_wit_4.
Axiom proof_of_OSSemQuery_partial_solve_wit_1_pure : OSSemQuery_partial_solve_wit_1_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_1 : OSSemQuery_partial_solve_wit_1.
Axiom proof_of_OSSemQuery_partial_solve_wit_2_pure : OSSemQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_2 : OSSemQuery_partial_solve_wit_2.
Axiom proof_of_OSSemQuery_partial_solve_wit_3_pure : OSSemQuery_partial_solve_wit_3_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_3 : OSSemQuery_partial_solve_wit_3.
Axiom proof_of_OSSemQuery_partial_solve_wit_4_pure : OSSemQuery_partial_solve_wit_4_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_4 : OSSemQuery_partial_solve_wit_4.
Axiom proof_of_OSSemQuery_partial_solve_wit_5_pure : OSSemQuery_partial_solve_wit_5_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_5 : OSSemQuery_partial_solve_wit_5.
Axiom proof_of_OSSemQuery_partial_solve_wit_6_pure : OSSemQuery_partial_solve_wit_6_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_6 : OSSemQuery_partial_solve_wit_6.
Axiom proof_of_OSSemQuery_partial_solve_wit_7_pure : OSSemQuery_partial_solve_wit_7_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_7 : OSSemQuery_partial_solve_wit_7.
Axiom proof_of_OSSemQuery_partial_solve_wit_8 : OSSemQuery_partial_solve_wit_8.
Axiom proof_of_OSSemQuery_partial_solve_wit_9_pure : OSSemQuery_partial_solve_wit_9_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_9 : OSSemQuery_partial_solve_wit_9.
Axiom proof_of_OSSemQuery_partial_solve_wit_10_pure : OSSemQuery_partial_solve_wit_10_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_10 : OSSemQuery_partial_solve_wit_10.
Axiom proof_of_OSSemQuery_partial_solve_wit_11_pure : OSSemQuery_partial_solve_wit_11_pure.
Axiom proof_of_OSSemQuery_partial_solve_wit_11 : OSSemQuery_partial_solve_wit_11.
Axiom proof_of_OSSemQuery_partial_solve_wit_12 : OSSemQuery_partial_solve_wit_12.
Axiom proof_of_OSSemQuery_which_implies_wit_1 : OSSemQuery_which_implies_wit_1.
Axiom proof_of_OSSemQuery_which_implies_wit_2 : OSSemQuery_which_implies_wit_2.
Axiom proof_of_OSSemQuery_which_implies_wit_3 : OSSemQuery_which_implies_wit_3.
Axiom proof_of_OSSemQuery_which_implies_wit_4 : OSSemQuery_which_implies_wit_4.
Axiom proof_of_OSSemQuery_which_implies_wit_5 : OSSemQuery_which_implies_wit_5.
Axiom proof_of_OSSemQuery_which_implies_wit_6 : OSSemQuery_which_implies_wit_6.
Axiom proof_of_OSSemQuery_which_implies_wit_7 : OSSemQuery_which_implies_wit_7.
Axiom proof_of_OSSemQuery_which_implies_wit_8 : OSSemQuery_which_implies_wit_8.
Axiom proof_of_OSSemQuery_which_implies_wit_9 : OSSemQuery_which_implies_wit_9.

End VC_Correct.
