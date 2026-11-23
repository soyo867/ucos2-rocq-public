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
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_query_return_spec.
Local Open Scope sac.

(*----- Function OSMutexQuery -----*)

Definition OSMutexQuery_safety_wit_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_2 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_3 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_4 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_5 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr > 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_6 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_7 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_8 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_9 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_10 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (p_mutex_data_pre <> 0)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_11 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (p_mutex_data_pre <> 0)) (PreH16 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_12 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_13 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_14 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (p_mutex_data_pre <> 0)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_15 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (p_mutex_data_pre <> 0)) (PreH16 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_16 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_17 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre <> 0)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_18 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre <> 0)) (PreH17 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_19 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_20 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH3 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_mutex_data_pre = pd)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (isr >= 0)) (PreH20 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH21 : (isr <= 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_21 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) <> 4)) (PreH2 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH3 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_mutex_data_pre = pd)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (isr >= 0)) (PreH20 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH21 : (isr <= 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ False ”
.

Definition OSMutexQuery_safety_wit_22 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH5 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (p_mutex_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mutex_data_pre = pd)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH23 : (isr <= 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_mutex_data_pre <> 0)) (PreH26 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_23 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH6 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (p_mutex_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (pevent_pre = pe)) (PreH20 : (p_mutex_data_pre = pd)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH24 : (isr <= 0)) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= cnt) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH6 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (p_mutex_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (pevent_pre = pe)) (PreH20 : (p_mutex_data_pre = pd)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH24 : (isr <= 0)) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= cnt) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexQuery_safety_wit_23_split_goal_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH6 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (p_mutex_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (pevent_pre = pe)) (PreH20 : (p_mutex_data_pre = pd)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH24 : (isr <= 0)) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= cnt) ”
.

Definition OSMutexQuery_safety_wit_23_split_goal_2 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH6 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (p_mutex_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (pevent_pre = pe)) (PreH20 : (p_mutex_data_pre = pd)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH24 : (isr <= 0)) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (8 <= 31) ”
.

Definition OSMutexQuery_safety_wit_23_split_goal_3 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH6 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (p_mutex_data_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (pevent_pre = pe)) (PreH20 : (p_mutex_data_pre = pd)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH24 : (isr <= 0)) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= 8) ”
.

Definition OSMutexQuery_safety_wit_24 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_25 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_26 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_27 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_28 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((Z.land cnt 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH14 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (p_mutex_data_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (isr <= 0)) (PreH22 : (0 <= isr)) (PreH23 : (isr <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (isr = (intNesting ((before.(IntrState) ))))) (PreH27 : (pevent_pre = pe)) (PreH28 : (p_mutex_data_pre = pd)) (PreH29 : (isr = (intNesting ((before.(IntrState) ))))) (PreH30 : (isr >= 0)) (PreH31 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH32 : (isr <= 0)) (PreH33 : (pevent_pre <> 0)) (PreH34 : (p_mutex_data_pre <> 0)) (PreH35 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OSMutexQuery_safety_wit_29 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((Z.land cnt 255) <> 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH14 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (p_mutex_data_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (isr <= 0)) (PreH22 : (0 <= isr)) (PreH23 : (isr <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (isr = (intNesting ((before.(IntrState) ))))) (PreH27 : (pevent_pre = pe)) (PreH28 : (p_mutex_data_pre = pd)) (PreH29 : (isr = (intNesting ((before.(IntrState) ))))) (PreH30 : (isr >= 0)) (PreH31 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH32 : (isr <= 0)) (PreH33 : (pevent_pre <> 0)) (PreH34 : (p_mutex_data_pre <> 0)) (PreH35 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OSMutexQuery_safety_wit_30 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt 255) = 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_safety_wit_31 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt 255) <> 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexQuery_entail_wit_1_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mutex_data_pre = pd)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr >= 0)) (PreH6 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_mutex_data_pre <> 0)) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_entail_wit_1_2 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mutex_data_pre = pd)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr >= 0)) (PreH6 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_mutex_data_pre <> 0)) (PreH10 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <> 4) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
.

Definition OSMutexQuery_entail_wit_1_3 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mutex_data_pre = pd)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr >= 0)) (PreH6 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre = 0) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
.

Definition OSMutexQuery_entail_wit_1_4 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mutex_data_pre = pd)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr >= 0)) (PreH6 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
.

Definition OSMutexQuery_entail_wit_1_5 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mutex_data_pre = pd)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr >= 0)) (PreH6 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH7 : (isr > 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr > 0) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (pevent_pre = pe)) (PreH5 : (p_mutex_data_pre = pd)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr >= 0)) (PreH8 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH9 : (isr > 0)) ,
  TT && emp 
|--
  “ (isr <= 255) ”
  &&  emp
).

Definition OSMutexQuery_entail_wit_1_5_split_goal_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (pevent_pre = pe)) (PreH5 : (p_mutex_data_pre = pd)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr >= 0)) (PreH8 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH9 : (isr > 0)) ,
  (isr <= 255)
.

Definition OSMutexQuery_entail_wit_2_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (p_mutex_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr <= 0)) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_mutex_data_pre = pd)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr >= 0)) (PreH17 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH18 : (isr <= 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_entail_wit_2_2 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (p_mutex_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr <= 0)) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_mutex_data_pre = pd)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr >= 0)) (PreH17 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH18 : (isr <= 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <> 4) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (p_mutex_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr <= 0)) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_mutex_data_pre = pd)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr >= 0)) (PreH17 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH18 : (isr <= 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  TT && emp 
|--
  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ”
  &&  emp
).

Definition OSMutexQuery_entail_wit_2_2_split_goal_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (p_mutex_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr <= 0)) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_mutex_data_pre = pd)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr >= 0)) (PreH17 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH18 : (isr <= 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  ((encode_event_type ((eventType (observed)))) <= 255)
.

Definition OSMutexQuery_entail_wit_2_2_split_goal_2 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (p_mutex_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr <= 0)) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (pevent_pre = pe)) (PreH14 : (p_mutex_data_pre = pd)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (isr >= 0)) (PreH17 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH18 : (isr <= 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (0 <= (encode_event_type ((eventType (observed)))))
.

Definition OSMutexQuery_entail_wit_3_1 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) (0)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt_2: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) (0)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt_2: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
).

Definition OSMutexQuery_entail_wit_3_2 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) (0)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry_2: UCOS2_Verify_State)  (current_2: OSEventAbstractState)  (cnt_3: Z)  (grp_2: Z)  (evtL_2: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry_2 eid observed current_2 pd cnt_3 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) (0)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry_2: UCOS2_Verify_State)  (current_2: OSEventAbstractState)  (cnt_3: Z)  (grp_2: Z)  (evtL_2: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry_2 eid observed current_2 pd cnt_3 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
).

Definition OSMutexQuery_entail_wit_4_1 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (pdest_v_2: Z) (psrc_v_2: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest_v_2 = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (i < 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : ((Z.land cnt 255) = 255)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH20 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH21 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr <= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (isr = (intNesting ((before.(IntrState) ))))) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (isr <= 0)) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (pevent_pre = pe)) (PreH35 : (p_mutex_data_pre = pd)) (PreH36 : (isr = (intNesting ((before.(IntrState) ))))) (PreH37 : (isr >= 0)) (PreH38 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH39 : (isr <= 0)) (PreH40 : (pevent_pre <> 0)) (PreH41 : (p_mutex_data_pre <> 0)) (PreH42 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt_2: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((psrc_v + 1 ) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((pdest_v + 1 ) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (pdest_v_2: Z) (psrc_v_2: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest_v_2 = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (i < 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : ((Z.land cnt 255) = 255)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH20 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH21 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr <= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (isr = (intNesting ((before.(IntrState) ))))) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (isr <= 0)) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (pevent_pre = pe)) (PreH35 : (p_mutex_data_pre = pd)) (PreH36 : (isr = (intNesting ((before.(IntrState) ))))) (PreH37 : (isr >= 0)) (PreH38 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH39 : (isr <= 0)) (PreH40 : (pevent_pre <> 0)) (PreH41 : (p_mutex_data_pre <> 0)) (PreH42 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt_2: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((psrc_v + 1 ) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((pdest_v + 1 ) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
).

Definition OSMutexQuery_entail_wit_4_2 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (pdest_v_2: Z) (psrc_v_2: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest_v_2 = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (i < 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : ((Z.land cnt 255) <> 255)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH20 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH21 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr <= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (isr = (intNesting ((before.(IntrState) ))))) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (isr <= 0)) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (pevent_pre = pe)) (PreH35 : (p_mutex_data_pre = pd)) (PreH36 : (isr = (intNesting ((before.(IntrState) ))))) (PreH37 : (isr >= 0)) (PreH38 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH39 : (isr <= 0)) (PreH40 : (pevent_pre <> 0)) (PreH41 : (p_mutex_data_pre <> 0)) (PreH42 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry_2: UCOS2_Verify_State)  (current_2: OSEventAbstractState)  (cnt_3: Z)  (grp_2: Z)  (evtL_2: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((psrc_v + 1 ) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((pdest_v + 1 ) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_3 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (pdest_v_2: Z) (psrc_v_2: Z) (entry_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (cnt_4: Z) (grp_3: Z) (evtL_3: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest_v_2 = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (i < 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : ((Z.land cnt 255) <> 255)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH20 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH21 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr <= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (isr = (intNesting ((before.(IntrState) ))))) (PreH26 : (p_mutex_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (isr <= 0)) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (pevent_pre = pe)) (PreH35 : (p_mutex_data_pre = pd)) (PreH36 : (isr = (intNesting ((before.(IntrState) ))))) (PreH37 : (isr >= 0)) (PreH38 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH39 : (isr <= 0)) (PreH40 : (pevent_pre <> 0)) (PreH41 : (p_mutex_data_pre <> 0)) (PreH42 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_3 eid observed current_3 pd cnt_4 grp_3 evtL_3 )
  **  (store_oseventtbl sg pe evtL_3 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_3) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (entry_2: UCOS2_Verify_State)  (current_2: OSEventAbstractState)  (cnt_3: Z)  (grp_2: Z)  (evtL_2: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((psrc_v + 1 ) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((pdest_v + 1 ) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_3 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) ((i + 1 ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
).

Definition OSMutexQuery_return_wit_1 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt_2: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_3: Z) (grp_2: Z) (evtL_2: (@list Z)) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt_2 255) = 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry) (after_2)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current_2) (cnt_3) (grp_2) (evtL_2)) )
  **  (mutex_query_output_fields pd cnt_3 grp_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (0)) X ) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((encode_event_type ((eventType (current)))) = 4) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (0) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (mutex_query_return_snapshot (critical) (sg) (invocation) (pe) (pd) (before) (after) (eid) (current) (cnt) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") evtL )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt_2: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_3: Z) (grp_2: Z) (evtL_2: (@list Z)) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt_2 255) = 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry) (after_2)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current_2) (cnt_3) (grp_2) (evtL_2)) )
  **  (mutex_query_output_fields pd cnt_3 grp_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (0)) X ) ” 
  &&  “ ((encode_event_type ((eventType (current)))) = 4) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (0) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (mutex_query_return_snapshot (critical) (sg) (invocation) (pe) (pd) (before) (after) (eid) (current) (cnt) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") evtL )
).

Definition OSMutexQuery_return_wit_2 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt_2: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_3: Z) (grp_2: Z) (evtL_2: (@list Z)) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt_2 255) <> 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry) (after_2)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current_2) (cnt_3) (grp_2) (evtL_2)) )
  **  (mutex_query_output_fields pd cnt_3 grp_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (0)) X ) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((encode_event_type ((eventType (current)))) = 4) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (0) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (mutex_query_return_snapshot (critical) (sg) (invocation) (pe) (pd) (before) (after) (eid) (current) (cnt) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") evtL )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt_2: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_3: Z) (grp_2: Z) (evtL_2: (@list Z)) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt_2 255) <> 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry) (after_2)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current_2) (cnt_3) (grp_2) (evtL_2)) )
  **  (mutex_query_output_fields pd cnt_3 grp_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (0)) X ) ” 
  &&  “ ((encode_event_type ((eventType (current)))) = 4) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (0) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (mutex_query_return_snapshot (critical) (sg) (invocation) (pe) (pd) (before) (after) (eid) (current) (cnt) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") evtL )
).

Definition OSMutexQuery_return_wit_3 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) <> 4)) (PreH2 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH3 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_mutex_data_pre = pd)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (isr >= 0)) (PreH20 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH21 : (isr <= 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (1)) X ) ” 
  &&  “ (1 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (1) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) <> 4)) (PreH2 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH3 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_mutex_data_pre = pd)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (isr >= 0)) (PreH20 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH21 : (isr <= 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (1)) X ) ” 
  &&  “ (1 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (1) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSMutexQuery_return_wit_4 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (9)) X ) ” 
  &&  “ (9 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (9) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (9)) X ) ” 
  &&  “ (9 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (9) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSMutexQuery_return_wit_5 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (4)) X ) ” 
  &&  “ (4 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (4) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (pevent_pre = pe)) (PreH9 : (p_mutex_data_pre = pd)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr >= 0)) (PreH12 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent_pre = 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (4)) X ) ” 
  &&  “ (4 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (4) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSMutexQuery_return_wit_6 := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr > 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (6)) X ) ” 
  &&  “ (6 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (6) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mutex_data_pre = pd)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr >= 0)) (PreH11 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH12 : (isr > 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (after)) (return (6)) X ) ” 
  &&  “ (6 <> 0) ”
  &&  (coq_prop (mutex_query_return_post_prop (critical) (sg) (invocation) (pe) (pd) (before) (6) (after)) )
  **  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSMutexQuery_partial_solve_wit_1_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_1_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr > 0)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr > 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
.

Definition OSMutexQuery_partial_solve_wit_1 := OSMutexQuery_partial_solve_wit_1_pure -> OSMutexQuery_partial_solve_wit_1_aux.

Definition OSMutexQuery_partial_solve_wit_2_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_2_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre = 0)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
.

Definition OSMutexQuery_partial_solve_wit_2 := OSMutexQuery_partial_solve_wit_2_pure -> OSMutexQuery_partial_solve_wit_2_aux.

Definition OSMutexQuery_partial_solve_wit_3_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (p_mutex_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_3_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (p_mutex_data_pre = 0)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre = 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
.

Definition OSMutexQuery_partial_solve_wit_3 := OSMutexQuery_partial_solve_wit_3_pure -> OSMutexQuery_partial_solve_wit_3_aux.

Definition OSMutexQuery_partial_solve_wit_4_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_4_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <> 4) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
.

Definition OSMutexQuery_partial_solve_wit_4 := OSMutexQuery_partial_solve_wit_4_pure -> OSMutexQuery_partial_solve_wit_4_aux.

Definition OSMutexQuery_partial_solve_wit_5_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_5_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mutex_data_pre = pd)) (PreH3 : (isr = (intNesting ((before.(IntrState) ))))) (PreH4 : (isr >= 0)) (PreH5 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH6 : (isr <= 0)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_5 := OSMutexQuery_partial_solve_wit_5_pure -> OSMutexQuery_partial_solve_wit_5_aux.

Definition OSMutexQuery_partial_solve_wit_6_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre <> 0)) (PreH17 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_6_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre <> 0)) (PreH17 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <> 4) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
.

Definition OSMutexQuery_partial_solve_wit_6 := OSMutexQuery_partial_solve_wit_6_pure -> OSMutexQuery_partial_solve_wit_6_aux.

Definition OSMutexQuery_partial_solve_wit_7_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre <> 0)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexQuery_partial_solve_wit_7_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mutex_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (pevent_pre = pe)) (PreH10 : (p_mutex_data_pre = pd)) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH14 : (isr <= 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mutex_data_pre <> 0)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_7 := OSMutexQuery_partial_solve_wit_7_pure -> OSMutexQuery_partial_solve_wit_7_aux.

Definition OSMutexQuery_partial_solve_wit_8_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (p_mutex_data_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mutex_data_pre = pd)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (isr >= 0)) (PreH14 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH15 : (isr <= 0)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_mutex_data_pre <> 0)) (PreH18 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
.

Definition OSMutexQuery_partial_solve_wit_8_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (p_mutex_data_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mutex_data_pre = pd)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (isr >= 0)) (PreH14 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH15 : (isr <= 0)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_mutex_data_pre <> 0)) (PreH18 : ((encode_event_type ((eventType (observed)))) <> 4)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <> 4) ”
  &&  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_8 := OSMutexQuery_partial_solve_wit_8_pure -> OSMutexQuery_partial_solve_wit_8_aux.

Definition OSMutexQuery_partial_solve_wit_9_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (p_mutex_data_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mutex_data_pre = pd)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (isr >= 0)) (PreH14 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH15 : (isr <= 0)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_mutex_data_pre <> 0)) (PreH18 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ”
.

Definition OSMutexQuery_partial_solve_wit_9_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (p_mutex_data_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mutex_data_pre = pd)) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (isr >= 0)) (PreH14 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH15 : (isr <= 0)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (p_mutex_data_pre <> 0)) (PreH18 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_9 := OSMutexQuery_partial_solve_wit_9_pure -> OSMutexQuery_partial_solve_wit_9_aux.

Definition OSMutexQuery_partial_solve_wit_10_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH3 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_mutex_data_pre = pd)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (isr >= 0)) (PreH20 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH21 : (isr <= 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
.

Definition OSMutexQuery_partial_solve_wit_10_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH3 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH4 : (isr = (intNesting ((before.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((before.(IntrState) ))))) (PreH8 : (p_mutex_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (isr = (intNesting ((before.(IntrState) ))))) (PreH16 : (pevent_pre = pe)) (PreH17 : (p_mutex_data_pre = pd)) (PreH18 : (isr = (intNesting ((before.(IntrState) ))))) (PreH19 : (isr >= 0)) (PreH20 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH21 : (isr <= 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_10 := OSMutexQuery_partial_solve_wit_10_pure -> OSMutexQuery_partial_solve_wit_10_aux.

Definition OSMutexQuery_partial_solve_wit_11_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH5 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (p_mutex_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mutex_data_pre = pd)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH23 : (isr <= 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_mutex_data_pre <> 0)) (PreH26 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ”
.

Definition OSMutexQuery_partial_solve_wit_11_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH5 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (p_mutex_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mutex_data_pre = pd)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH23 : (isr <= 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_mutex_data_pre <> 0)) (PreH26 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_11 := OSMutexQuery_partial_solve_wit_11_pure -> OSMutexQuery_partial_solve_wit_11_aux.

Definition OSMutexQuery_partial_solve_wit_12_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH5 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (p_mutex_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mutex_data_pre = pd)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH23 : (isr <= 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_mutex_data_pre <> 0)) (PreH26 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_partial_solve_wit_12_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (val_in: Z) (prio_in: Z) (pcp_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH5 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH6 : (isr = (intNesting ((before.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (p_mutex_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mutex_data_pre = pd)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH23 : (isr <= 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_mutex_data_pre <> 0)) (PreH26 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_12 := OSMutexQuery_partial_solve_wit_12_pure -> OSMutexQuery_partial_solve_wit_12_aux.

Definition OSMutexQuery_partial_solve_wit_13_pure := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH7 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (isr <= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (p_mutex_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (isr <= 0)) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (pevent_pre = pe)) (PreH21 : (p_mutex_data_pre = pd)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr >= 0)) (PreH24 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH25 : (isr <= 0)) (PreH26 : (pevent_pre <> 0)) (PreH27 : (p_mutex_data_pre <> 0)) (PreH28 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (0 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (0 = (decode_OSValue_from_cnt (cnt))) ”
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ (0 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ”
).

Definition OSMutexQuery_partial_solve_wit_13_pure_split_goal_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 = (decode_OSValue_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_13_pure_split_goal_2 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_13_pure_split_goal_3 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_13_pure_split_goal_4 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (0 = (decode_OSValue_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_13_pure_split_goal_5 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_13_pure_split_goal_6 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_13_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH7 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (isr <= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (p_mutex_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (isr <= 0)) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (pevent_pre = pe)) (PreH21 : (p_mutex_data_pre = pd)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr >= 0)) (PreH24 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH25 : (isr <= 0)) (PreH26 : (pevent_pre <> 0)) (PreH27 : (p_mutex_data_pre <> 0)) (PreH28 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (0 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (0 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_13 := OSMutexQuery_partial_solve_wit_13_pure -> OSMutexQuery_partial_solve_wit_13_aux.

Definition OSMutexQuery_partial_solve_wit_14_pure := 
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) = 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH7 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (isr <= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (p_mutex_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (isr <= 0)) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (pevent_pre = pe)) (PreH21 : (p_mutex_data_pre = pd)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr >= 0)) (PreH24 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH25 : (isr <= 0)) (PreH26 : (pevent_pre <> 0)) (PreH27 : (p_mutex_data_pre <> 0)) (PreH28 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (1 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (1 = (decode_OSValue_from_cnt (cnt))) ”
) \/
(
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (1 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ (1 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ”
).

Definition OSMutexQuery_partial_solve_wit_14_pure_split_goal_1 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (1 = (decode_OSValue_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_14_pure_split_goal_2 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_14_pure_split_goal_3 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_14_pure_split_goal_4 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (1 = (decode_OSValue_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_14_pure_split_goal_5 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_14_pure_split_goal_6 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ”
.

Definition OSMutexQuery_partial_solve_wit_14_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (grp_pd_in: Z) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) = 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH7 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH8 : (isr = (intNesting ((before.(IntrState) ))))) (PreH9 : (isr <= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (isr = (intNesting ((before.(IntrState) ))))) (PreH12 : (p_mutex_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (isr <= 0)) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (pevent_pre = pe)) (PreH21 : (p_mutex_data_pre = pd)) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (isr >= 0)) (PreH24 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH25 : (isr <= 0)) (PreH26 : (pevent_pre <> 0)) (PreH27 : (p_mutex_data_pre <> 0)) (PreH28 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (1 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (decode_PCP_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = (decode_OwnerPrio_from_cnt (cnt))) ” 
  &&  “ (1 = (decode_OSValue_from_cnt (cnt))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_14 := OSMutexQuery_partial_solve_wit_14_pure -> OSMutexQuery_partial_solve_wit_14_aux.

Definition OSMutexQuery_partial_solve_wit_15_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) <> 255)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH7 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH8 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (p_mutex_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr <= 0)) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (pevent_pre = pe)) (PreH22 : (p_mutex_data_pre = pd)) (PreH23 : (isr = (intNesting ((before.(IntrState) ))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH26 : (isr <= 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_mutex_data_pre <> 0)) (PreH29 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_partial_solve_wit_15_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) <> 255)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH7 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH8 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (p_mutex_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr <= 0)) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (pevent_pre = pe)) (PreH22 : (p_mutex_data_pre = pd)) (PreH23 : (isr = (intNesting ((before.(IntrState) ))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH26 : (isr <= 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_mutex_data_pre <> 0)) (PreH29 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_15 := OSMutexQuery_partial_solve_wit_15_pure -> OSMutexQuery_partial_solve_wit_15_aux.

Definition OSMutexQuery_partial_solve_wit_16_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH7 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH8 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (p_mutex_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr <= 0)) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (pevent_pre = pe)) (PreH22 : (p_mutex_data_pre = pd)) (PreH23 : (isr = (intNesting ((before.(IntrState) ))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH26 : (isr <= 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_mutex_data_pre <> 0)) (PreH29 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_partial_solve_wit_16_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH7 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH8 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH9 : (isr = (intNesting ((before.(IntrState) ))))) (PreH10 : (isr <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (isr = (intNesting ((before.(IntrState) ))))) (PreH13 : (p_mutex_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr <= 0)) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (pevent_pre = pe)) (PreH22 : (p_mutex_data_pre = pd)) (PreH23 : (isr = (intNesting ((before.(IntrState) ))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH26 : (isr <= 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_mutex_data_pre <> 0)) (PreH29 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
.

Definition OSMutexQuery_partial_solve_wit_16 := OSMutexQuery_partial_solve_wit_16_pure -> OSMutexQuery_partial_solve_wit_16_aux.

Definition OSMutexQuery_partial_solve_wit_17 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) <> 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_18 := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH9 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH10 : (isr = (intNesting ((before.(IntrState) ))))) (PreH11 : (isr <= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (isr = (intNesting ((before.(IntrState) ))))) (PreH14 : (p_mutex_data_pre <> 0)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr <= 0)) (PreH17 : (0 <= isr)) (PreH18 : (isr <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (isr = (intNesting ((before.(IntrState) ))))) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_mutex_data_pre = pd)) (PreH24 : (isr = (intNesting ((before.(IntrState) ))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH27 : (isr <= 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_mutex_data_pre <> 0)) (PreH30 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_19_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) <> 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSMutexQuery_partial_solve_wit_19_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) <> 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_19 := OSMutexQuery_partial_solve_wit_19_pure -> OSMutexQuery_partial_solve_wit_19_aux.

Definition OSMutexQuery_partial_solve_wit_20_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) = 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSMutexQuery_partial_solve_wit_20_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) = 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_20 := OSMutexQuery_partial_solve_wit_20_pure -> OSMutexQuery_partial_solve_wit_20_aux.

Definition OSMutexQuery_partial_solve_wit_21_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((Z.land cnt 255) <> 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH18 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (isr <= 0)) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (0 <= UINT_MAX)) (PreH29 : (0 >= 0)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (pevent_pre = pe)) (PreH32 : (p_mutex_data_pre = pd)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (isr >= 0)) (PreH35 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH36 : (isr <= 0)) (PreH37 : (pevent_pre <> 0)) (PreH38 : (p_mutex_data_pre <> 0)) (PreH39 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSMutexQuery_partial_solve_wit_21_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((Z.land cnt 255) <> 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH18 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (isr <= 0)) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (0 <= UINT_MAX)) (PreH29 : (0 >= 0)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (pevent_pre = pe)) (PreH32 : (p_mutex_data_pre = pd)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (isr >= 0)) (PreH35 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH36 : (isr <= 0)) (PreH37 : (pevent_pre <> 0)) (PreH38 : (p_mutex_data_pre <> 0)) (PreH39 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  (((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_21 := OSMutexQuery_partial_solve_wit_21_pure -> OSMutexQuery_partial_solve_wit_21_aux.

Definition OSMutexQuery_partial_solve_wit_22_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((Z.land cnt 255) = 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH18 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (isr <= 0)) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (0 <= UINT_MAX)) (PreH29 : (0 >= 0)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (pevent_pre = pe)) (PreH32 : (p_mutex_data_pre = pd)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (isr >= 0)) (PreH35 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH36 : (isr <= 0)) (PreH37 : (pevent_pre <> 0)) (PreH38 : (p_mutex_data_pre <> 0)) (PreH39 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSMutexQuery_partial_solve_wit_22_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest_v: Z) (psrc_v: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((Z.land cnt 255) = 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH18 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (isr = (intNesting ((before.(IntrState) ))))) (PreH23 : (p_mutex_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (isr <= 0)) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (0 <= UINT_MAX)) (PreH29 : (0 >= 0)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (pevent_pre = pe)) (PreH32 : (p_mutex_data_pre = pd)) (PreH33 : (isr = (intNesting ((before.(IntrState) ))))) (PreH34 : (isr >= 0)) (PreH35 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH36 : (isr <= 0)) (PreH37 : (pevent_pre <> 0)) (PreH38 : (p_mutex_data_pre <> 0)) (PreH39 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  (((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_22 := OSMutexQuery_partial_solve_wit_22_pure -> OSMutexQuery_partial_solve_wit_22_aux.

Definition OSMutexQuery_partial_solve_wit_23_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) <> 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_partial_solve_wit_23_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) <> 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_23 := OSMutexQuery_partial_solve_wit_23_pure -> OSMutexQuery_partial_solve_wit_23_aux.

Definition OSMutexQuery_partial_solve_wit_24_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) = 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_partial_solve_wit_24_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Z.land cnt 255) = 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH15 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH16 : (isr = (intNesting ((before.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (isr = (intNesting ((before.(IntrState) ))))) (PreH20 : (p_mutex_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (isr <= 0)) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (isr = (intNesting ((before.(IntrState) ))))) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_mutex_data_pre = pd)) (PreH30 : (isr = (intNesting ((before.(IntrState) ))))) (PreH31 : (isr >= 0)) (PreH32 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH33 : (isr <= 0)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (p_mutex_data_pre <> 0)) (PreH36 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_24 := OSMutexQuery_partial_solve_wit_24_pure -> OSMutexQuery_partial_solve_wit_24_aux.

Definition OSMutexQuery_partial_solve_wit_25_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt 255) = 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMutexQuery_partial_solve_wit_25_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt 255) = 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_25 := OSMutexQuery_partial_solve_wit_25_pure -> OSMutexQuery_partial_solve_wit_25_aux.

Definition OSMutexQuery_partial_solve_wit_26_pure := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt 255) <> 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMutexQuery_partial_solve_wit_26_aux := 
forall (p_mutex_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (outL_in: (@list Z)) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cnt: Z) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (cnt_2: Z) (grp: Z) (evtL: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Z.land cnt 255) <> 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (0 <= (encode_event_type ((eventType (observed)))))) (PreH16 : ((encode_event_type ((eventType (observed)))) <= 255)) (PreH17 : (isr = (intNesting ((before.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (isr = (intNesting ((before.(IntrState) ))))) (PreH21 : (p_mutex_data_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (isr <= 0)) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (isr = (intNesting ((before.(IntrState) ))))) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mutex_data_pre = pd)) (PreH31 : (isr = (intNesting ((before.(IntrState) ))))) (PreH32 : (isr >= 0)) (PreH33 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X )) (PreH34 : (isr <= 0)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mutex_data_pre <> 0)) (PreH37 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (0 <= (encode_event_type ((eventType (observed))))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) <= 255) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mutex_data_pre = pd) ” 
  &&  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_query_return_program (critical) (sg) (invocation) (pe) (pd))))) (mutex_query_observe_error)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mutex_data_pre <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexQuery_partial_solve_wit_26 := OSMutexQuery_partial_solve_wit_26_pure -> OSMutexQuery_partial_solve_wit_26_aux.

Definition OSMutexQuery_which_implies_wit_1 := 
(
forall (isr: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
) \/
(
forall (isr: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
).

Definition OSMutexQuery_which_implies_wit_1_split_goal_spatial := 
forall (isr: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
.

Definition OSMutexQuery_which_implies_wit_2 := 
(
forall (isr: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
) \/
(
forall (isr: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
).

Definition OSMutexQuery_which_implies_wit_2_split_goal_spatial := 
forall (isr: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
.

Definition OSMutexQuery_which_implies_wit_3 := 
(
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) ,
  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
|--
  “ (isr = (intNesting ((before.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
) \/
(
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) ,
  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
).

Definition OSMutexQuery_which_implies_wit_3_split_goal_1 := 
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) ,
  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_which_implies_wit_3_split_goal_spatial := 
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) ,
  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
.

Definition OSMutexQuery_which_implies_wit_4 := 
(
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
) \/
(
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
).

Definition OSMutexQuery_which_implies_wit_4_split_goal_1 := 
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexQuery_which_implies_wit_4_split_goal_spatial := 
forall (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (isr = (intNesting ((before.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pd <> 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
|--
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
.

Definition OSMutexQuery_which_implies_wit_5 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
).

Definition OSMutexQuery_which_implies_wit_6 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  (used_event_rest_no_type_cnt_ptr sg (entry_2.(TskState) ) pe eid current_2 )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt)))
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  (used_event_rest_no_type_cnt_ptr sg (entry_2.(TskState) ) pe eid current_2 )
|--
  EX (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
).

Definition OSMutexQuery_which_implies_wit_7 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_oseventtbl sg pe evtL_2 )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  (store_oseventtbl sg pe evtL )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry_2) (eid) (current_2) (cnt_2) (grp_2) (evtL_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (interrupt_inv sg (entry_2.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry_2 eid )
  **  (mutex_query_event_unread sg (entry_2.(TskState) ) eid current_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_oseventtbl sg pe evtL_2 )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  (store_oseventtbl sg pe evtL )
).

Definition OSMutexQuery_which_implies_wit_8 := 
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (0)) )
) \/
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (0)) )
).

Definition OSMutexQuery_which_implies_wit_9 := 
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v: Z) (psrc_v: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) ((copy_prefix_list (evtL) (outL_in) (i))) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
) \/
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v: Z) (psrc_v: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) ((copy_prefix_list (evtL) (outL_in) (i))) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
).

Definition OSMutexQuery_which_implies_wit_10 := 
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v_2: Z) (psrc_v_2: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v_2 = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v_2 + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v_2 + 1 ))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((psrc_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL_2 i )
  **  ((pdest_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (pdest_v: Z)  (psrc_v: Z) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc_v = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest_v = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + 1 ))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) ((i + 1 ))) )
) \/
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pdest_v_2: Z) (psrc_v_2: Z) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (psrc_v_2 = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : (pdest_v_2 = (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  ((psrc_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL_2 i )
  **  ((pdest_v_2) # UChar  |-> (Znth (i) (evtL_2) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (cnt: Z)  (grp: Z)  (evtL: (@list Z)) ,
  “ ((pdest_v_2 + 1 ) = ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ ((psrc_v_2 + 1 ) = ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ ((pdest_v_2 + 1 ) = ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ ((psrc_v_2 + 1 ) = ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 )) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) ((i + 1 ))) )
).

Definition OSMutexQuery_which_implies_wit_11 := 
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
) \/
(
forall (outL_in: (@list Z)) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (evtL_2: (@list Z)) (grp_2: Z) (cnt_2: Z) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 )
  **  (store_oseventtbl sg pe evtL_2 )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL_2) (outL_in) (i)) )
|--
  EX (cnt: Z)  (grp: Z)  (evtL: (@list Z))  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
).

Module Type VC_Correct.


Axiom proof_of_OSMutexQuery_safety_wit_1 : OSMutexQuery_safety_wit_1.
Axiom proof_of_OSMutexQuery_safety_wit_2 : OSMutexQuery_safety_wit_2.
Axiom proof_of_OSMutexQuery_safety_wit_3 : OSMutexQuery_safety_wit_3.
Axiom proof_of_OSMutexQuery_safety_wit_4 : OSMutexQuery_safety_wit_4.
Axiom proof_of_OSMutexQuery_safety_wit_5 : OSMutexQuery_safety_wit_5.
Axiom proof_of_OSMutexQuery_safety_wit_6 : OSMutexQuery_safety_wit_6.
Axiom proof_of_OSMutexQuery_safety_wit_7 : OSMutexQuery_safety_wit_7.
Axiom proof_of_OSMutexQuery_safety_wit_8 : OSMutexQuery_safety_wit_8.
Axiom proof_of_OSMutexQuery_safety_wit_9 : OSMutexQuery_safety_wit_9.
Axiom proof_of_OSMutexQuery_safety_wit_10 : OSMutexQuery_safety_wit_10.
Axiom proof_of_OSMutexQuery_safety_wit_11 : OSMutexQuery_safety_wit_11.
Axiom proof_of_OSMutexQuery_safety_wit_12 : OSMutexQuery_safety_wit_12.
Axiom proof_of_OSMutexQuery_safety_wit_13 : OSMutexQuery_safety_wit_13.
Axiom proof_of_OSMutexQuery_safety_wit_14 : OSMutexQuery_safety_wit_14.
Axiom proof_of_OSMutexQuery_safety_wit_15 : OSMutexQuery_safety_wit_15.
Axiom proof_of_OSMutexQuery_safety_wit_16 : OSMutexQuery_safety_wit_16.
Axiom proof_of_OSMutexQuery_safety_wit_17 : OSMutexQuery_safety_wit_17.
Axiom proof_of_OSMutexQuery_safety_wit_18 : OSMutexQuery_safety_wit_18.
Axiom proof_of_OSMutexQuery_safety_wit_19 : OSMutexQuery_safety_wit_19.
Axiom proof_of_OSMutexQuery_safety_wit_20 : OSMutexQuery_safety_wit_20.
Axiom proof_of_OSMutexQuery_safety_wit_21 : OSMutexQuery_safety_wit_21.
Axiom proof_of_OSMutexQuery_safety_wit_22 : OSMutexQuery_safety_wit_22.
Axiom proof_of_OSMutexQuery_safety_wit_23 : OSMutexQuery_safety_wit_23.
Axiom proof_of_OSMutexQuery_safety_wit_24 : OSMutexQuery_safety_wit_24.
Axiom proof_of_OSMutexQuery_safety_wit_25 : OSMutexQuery_safety_wit_25.
Axiom proof_of_OSMutexQuery_safety_wit_26 : OSMutexQuery_safety_wit_26.
Axiom proof_of_OSMutexQuery_safety_wit_27 : OSMutexQuery_safety_wit_27.
Axiom proof_of_OSMutexQuery_safety_wit_28 : OSMutexQuery_safety_wit_28.
Axiom proof_of_OSMutexQuery_safety_wit_29 : OSMutexQuery_safety_wit_29.
Axiom proof_of_OSMutexQuery_safety_wit_30 : OSMutexQuery_safety_wit_30.
Axiom proof_of_OSMutexQuery_safety_wit_31 : OSMutexQuery_safety_wit_31.
Axiom proof_of_OSMutexQuery_entail_wit_1_1 : OSMutexQuery_entail_wit_1_1.
Axiom proof_of_OSMutexQuery_entail_wit_1_2 : OSMutexQuery_entail_wit_1_2.
Axiom proof_of_OSMutexQuery_entail_wit_1_3 : OSMutexQuery_entail_wit_1_3.
Axiom proof_of_OSMutexQuery_entail_wit_1_4 : OSMutexQuery_entail_wit_1_4.
Axiom proof_of_OSMutexQuery_entail_wit_1_5 : OSMutexQuery_entail_wit_1_5.
Axiom proof_of_OSMutexQuery_entail_wit_2_1 : OSMutexQuery_entail_wit_2_1.
Axiom proof_of_OSMutexQuery_entail_wit_2_2 : OSMutexQuery_entail_wit_2_2.
Axiom proof_of_OSMutexQuery_entail_wit_3_1 : OSMutexQuery_entail_wit_3_1.
Axiom proof_of_OSMutexQuery_entail_wit_3_2 : OSMutexQuery_entail_wit_3_2.
Axiom proof_of_OSMutexQuery_entail_wit_4_1 : OSMutexQuery_entail_wit_4_1.
Axiom proof_of_OSMutexQuery_entail_wit_4_2 : OSMutexQuery_entail_wit_4_2.
Axiom proof_of_OSMutexQuery_return_wit_1 : OSMutexQuery_return_wit_1.
Axiom proof_of_OSMutexQuery_return_wit_2 : OSMutexQuery_return_wit_2.
Axiom proof_of_OSMutexQuery_return_wit_3 : OSMutexQuery_return_wit_3.
Axiom proof_of_OSMutexQuery_return_wit_4 : OSMutexQuery_return_wit_4.
Axiom proof_of_OSMutexQuery_return_wit_5 : OSMutexQuery_return_wit_5.
Axiom proof_of_OSMutexQuery_return_wit_6 : OSMutexQuery_return_wit_6.
Axiom proof_of_OSMutexQuery_partial_solve_wit_1_pure : OSMutexQuery_partial_solve_wit_1_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_1 : OSMutexQuery_partial_solve_wit_1.
Axiom proof_of_OSMutexQuery_partial_solve_wit_2_pure : OSMutexQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_2 : OSMutexQuery_partial_solve_wit_2.
Axiom proof_of_OSMutexQuery_partial_solve_wit_3_pure : OSMutexQuery_partial_solve_wit_3_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_3 : OSMutexQuery_partial_solve_wit_3.
Axiom proof_of_OSMutexQuery_partial_solve_wit_4_pure : OSMutexQuery_partial_solve_wit_4_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_4 : OSMutexQuery_partial_solve_wit_4.
Axiom proof_of_OSMutexQuery_partial_solve_wit_5_pure : OSMutexQuery_partial_solve_wit_5_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_5 : OSMutexQuery_partial_solve_wit_5.
Axiom proof_of_OSMutexQuery_partial_solve_wit_6_pure : OSMutexQuery_partial_solve_wit_6_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_6 : OSMutexQuery_partial_solve_wit_6.
Axiom proof_of_OSMutexQuery_partial_solve_wit_7_pure : OSMutexQuery_partial_solve_wit_7_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_7 : OSMutexQuery_partial_solve_wit_7.
Axiom proof_of_OSMutexQuery_partial_solve_wit_8_pure : OSMutexQuery_partial_solve_wit_8_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_8 : OSMutexQuery_partial_solve_wit_8.
Axiom proof_of_OSMutexQuery_partial_solve_wit_9_pure : OSMutexQuery_partial_solve_wit_9_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_9 : OSMutexQuery_partial_solve_wit_9.
Axiom proof_of_OSMutexQuery_partial_solve_wit_10_pure : OSMutexQuery_partial_solve_wit_10_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_10 : OSMutexQuery_partial_solve_wit_10.
Axiom proof_of_OSMutexQuery_partial_solve_wit_11_pure : OSMutexQuery_partial_solve_wit_11_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_11 : OSMutexQuery_partial_solve_wit_11.
Axiom proof_of_OSMutexQuery_partial_solve_wit_12_pure : OSMutexQuery_partial_solve_wit_12_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_12 : OSMutexQuery_partial_solve_wit_12.
Axiom proof_of_OSMutexQuery_partial_solve_wit_13_pure : OSMutexQuery_partial_solve_wit_13_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_13 : OSMutexQuery_partial_solve_wit_13.
Axiom proof_of_OSMutexQuery_partial_solve_wit_14_pure : OSMutexQuery_partial_solve_wit_14_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_14 : OSMutexQuery_partial_solve_wit_14.
Axiom proof_of_OSMutexQuery_partial_solve_wit_15_pure : OSMutexQuery_partial_solve_wit_15_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_15 : OSMutexQuery_partial_solve_wit_15.
Axiom proof_of_OSMutexQuery_partial_solve_wit_16_pure : OSMutexQuery_partial_solve_wit_16_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_16 : OSMutexQuery_partial_solve_wit_16.
Axiom proof_of_OSMutexQuery_partial_solve_wit_17 : OSMutexQuery_partial_solve_wit_17.
Axiom proof_of_OSMutexQuery_partial_solve_wit_18 : OSMutexQuery_partial_solve_wit_18.
Axiom proof_of_OSMutexQuery_partial_solve_wit_19_pure : OSMutexQuery_partial_solve_wit_19_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_19 : OSMutexQuery_partial_solve_wit_19.
Axiom proof_of_OSMutexQuery_partial_solve_wit_20_pure : OSMutexQuery_partial_solve_wit_20_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_20 : OSMutexQuery_partial_solve_wit_20.
Axiom proof_of_OSMutexQuery_partial_solve_wit_21_pure : OSMutexQuery_partial_solve_wit_21_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_21 : OSMutexQuery_partial_solve_wit_21.
Axiom proof_of_OSMutexQuery_partial_solve_wit_22_pure : OSMutexQuery_partial_solve_wit_22_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_22 : OSMutexQuery_partial_solve_wit_22.
Axiom proof_of_OSMutexQuery_partial_solve_wit_23_pure : OSMutexQuery_partial_solve_wit_23_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_23 : OSMutexQuery_partial_solve_wit_23.
Axiom proof_of_OSMutexQuery_partial_solve_wit_24_pure : OSMutexQuery_partial_solve_wit_24_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_24 : OSMutexQuery_partial_solve_wit_24.
Axiom proof_of_OSMutexQuery_partial_solve_wit_25_pure : OSMutexQuery_partial_solve_wit_25_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_25 : OSMutexQuery_partial_solve_wit_25.
Axiom proof_of_OSMutexQuery_partial_solve_wit_26_pure : OSMutexQuery_partial_solve_wit_26_pure.
Axiom proof_of_OSMutexQuery_partial_solve_wit_26 : OSMutexQuery_partial_solve_wit_26.
Axiom proof_of_OSMutexQuery_which_implies_wit_1 : OSMutexQuery_which_implies_wit_1.
Axiom proof_of_OSMutexQuery_which_implies_wit_2 : OSMutexQuery_which_implies_wit_2.
Axiom proof_of_OSMutexQuery_which_implies_wit_3 : OSMutexQuery_which_implies_wit_3.
Axiom proof_of_OSMutexQuery_which_implies_wit_4 : OSMutexQuery_which_implies_wit_4.
Axiom proof_of_OSMutexQuery_which_implies_wit_5 : OSMutexQuery_which_implies_wit_5.
Axiom proof_of_OSMutexQuery_which_implies_wit_6 : OSMutexQuery_which_implies_wit_6.
Axiom proof_of_OSMutexQuery_which_implies_wit_7 : OSMutexQuery_which_implies_wit_7.
Axiom proof_of_OSMutexQuery_which_implies_wit_8 : OSMutexQuery_which_implies_wit_8.
Axiom proof_of_OSMutexQuery_which_implies_wit_9 : OSMutexQuery_which_implies_wit_9.
Axiom proof_of_OSMutexQuery_which_implies_wit_10 : OSMutexQuery_which_implies_wit_10.
Axiom proof_of_OSMutexQuery_which_implies_wit_11 : OSMutexQuery_which_implies_wit_11.

End VC_Correct.
