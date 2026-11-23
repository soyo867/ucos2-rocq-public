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
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Import MutexCreatePublication.
Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Import MutexCreatePublication.
Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSMutexCreate -----*)

Definition OSMutexCreate_safety_wit_1 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (perr_pre <> 0)) (PreH7 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 42)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_2 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_3 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_4_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_5_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_6_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (perr_pre <> 0)) (PreH14 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ False ”
.

Definition OSMutexCreate_safety_wit_7_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (perr_pre <> 0)) (PreH13 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ False ”
.

Definition OSMutexCreate_safety_wit_8_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : (prio_pre <> 255)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH14 : (prio_pre < 63)) (PreH15 : (prio_pre <> 255)) (PreH16 : (prio_pre = prio_in)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : (perr_pre <> 0)) (PreH20 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_9_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) (PreH8 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_2) (after)) )
  **  (closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_10_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) (PreH8 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_2) (after)) )
  **  (closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 40)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_11_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : (prio_pre <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH15 : (prio_pre < 63)) (PreH16 : (prio_pre <> 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (perr_pre <> 0)) (PreH21 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSMutexCreate_safety_wit_12_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : (prio_pre <> 255)) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (perr_pre <> 0)) (PreH27 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_13_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH12 : (prio_pre = 255)) (PreH13 : (prio_pre = prio_in)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in <= 255)) (PreH16 : (perr_pre <> 0)) (PreH17 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_14_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : ((free_head (sg) (entry_2)) = 0)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (prio_in <> 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in < 64)) (PreH9 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : (prio_pre <> 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre < 63)) (PreH24 : (prio_pre <> 255)) (PreH25 : (prio_pre = prio_in)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : (perr_pre <> 0)) (PreH29 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ False ”
.

Definition OSMutexCreate_safety_wit_15_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : ((free_head (sg) (entry)) = 0)) (PreH3 : (prio_in = 255)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (prio_pre = prio_in)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (perr_pre <> 0)) (PreH19 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ False ”
.

Definition OSMutexCreate_safety_wit_16_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry_3)) = 0)) (PreH8 : (prio_pre <> 255)) (PreH9 : ((free_head (sg) (entry_2)) = 0)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (prio_in <> 255)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in < 64)) (PreH23 : (prio_pre <> 255)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH28 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH30 : (prio_pre < 63)) (PreH31 : (prio_pre <> 255)) (PreH32 : (prio_pre = prio_in)) (PreH33 : (0 <= prio_in)) (PreH34 : (prio_in <= 255)) (PreH35 : (perr_pre <> 0)) (PreH36 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (head_residual sg entry_3 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (reserved_priority_table_missing sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_17_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry_5: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_5)) = 0)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH8 : (prio_in <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in < 64)) (PreH11 : ((free_head (sg) (entry_4)) = 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((free_head (sg) (entry_3)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : ((free_head (sg) (entry_2)) = 0)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in <= 255)) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH31 : (prio_in <> 255)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in < 64)) (PreH34 : (prio_pre <> 255)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH38 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH39 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH40 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH41 : (prio_pre < 63)) (PreH42 : (prio_pre <> 255)) (PreH43 : (prio_pre = prio_in)) (PreH44 : (0 <= prio_in)) (PreH45 : (prio_in <= 255)) (PreH46 : (perr_pre <> 0)) (PreH47 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_5) (after)) )
  **  (closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_18_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_3)) = 0)) (PreH5 : (prio_in = 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = 0)) (PreH10 : (prio_pre = 255)) (PreH11 : ((free_head (sg) (entry)) = 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_3) (after)) )
  **  (closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_19_priority_enabled := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexCreate_safety_wit_19_priority_enabled_split_goal_1 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ”
.

Definition OSMutexCreate_safety_wit_19_priority_enabled_split_goal_2 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ”
.

Definition OSMutexCreate_safety_wit_19_priority_enabled_split_goal_3 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (8 <= 31) ”
.

Definition OSMutexCreate_safety_wit_19_priority_enabled_split_goal_4 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= 8) ”
.

Definition OSMutexCreate_safety_wit_20_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH8 : ((free_head (sg) (entry)) <> 0)) (PreH9 : (prio_in = 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in <= 255)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH18 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (perr_pre <> 0)) (PreH25 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
.

Definition OSMutexCreate_safety_wit_21_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_22_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH8 : ((free_head (sg) (entry)) <> 0)) (PreH9 : (prio_in = 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in <= 255)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH18 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (perr_pre <> 0)) (PreH25 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_23_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH11 : ((free_head (sg) (entry_2)) <> 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : (prio_pre <> 255)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH30 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH31 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (perr_pre <> 0)) (PreH38 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) ((mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4))) (after)) )
  **  (closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_safety_wit_24_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) ((mutex_create_state (sg) (255) (eid) (rest) (entry_3))) (after)) )
  **  (closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_return_wit_1_priority_enabled := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_3)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : (prio_pre <> 255)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH30 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH31 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (perr_pre <> 0)) (PreH38 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) ((mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4))) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ ((free_head (sg) (entry)) = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_3)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : (prio_pre <> 255)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH30 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH31 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (perr_pre <> 0)) (PreH38 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) ((mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4))) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return ((free_head (sg) (entry)))) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) ((free_head (sg) (entry))) (0)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_2_priority_disabled := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) ((mutex_create_state (sg) (255) (eid) (rest) (entry_3))) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ ((free_head (sg) (entry)) = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) ((mutex_create_state (sg) (255) (eid) (rest) (entry_3))) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return ((free_head (sg) (entry)))) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) ((free_head (sg) (entry))) (0)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_3_priority_enabled := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry_5: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_5)) = 0)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH8 : (prio_in <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in < 64)) (PreH11 : ((free_head (sg) (entry_4)) = 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((free_head (sg) (entry_3)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : ((free_head (sg) (entry)) = 0)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in <= 255)) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH31 : (prio_in <> 255)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in < 64)) (PreH34 : (prio_pre <> 255)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH38 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH39 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH40 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH41 : (prio_pre < 63)) (PreH42 : (prio_pre <> 255)) (PreH43 : (prio_pre = prio_in)) (PreH44 : (0 <= prio_in)) (PreH45 : (prio_in <= 255)) (PreH46 : (perr_pre <> 0)) (PreH47 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_5) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 4)
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ ((free_head (sg) (entry)) = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry_5: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_5)) = 0)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH8 : (prio_in <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in < 64)) (PreH11 : ((free_head (sg) (entry_4)) = 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((free_head (sg) (entry_3)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : ((free_head (sg) (entry)) = 0)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in <= 255)) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH31 : (prio_in <> 255)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in < 64)) (PreH34 : (prio_pre <> 255)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH38 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH39 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH40 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH41 : (prio_pre < 63)) (PreH42 : (prio_pre <> 255)) (PreH43 : (prio_pre = prio_in)) (PreH44 : (0 <= prio_in)) (PreH45 : (prio_in <= 255)) (PreH46 : (perr_pre <> 0)) (PreH47 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_5) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return ((free_head (sg) (entry)))) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) ((free_head (sg) (entry))) (4)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_4_priority_disabled := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_3)) = 0)) (PreH5 : (prio_in = 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = 0)) (PreH10 : (prio_pre = 255)) (PreH11 : ((free_head (sg) (entry)) = 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_3) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 4)
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ ((free_head (sg) (entry)) = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_3)) = 0)) (PreH5 : (prio_in = 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = 0)) (PreH10 : (prio_pre = 255)) (PreH11 : ((free_head (sg) (entry)) = 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_3) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return ((free_head (sg) (entry)))) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) ((free_head (sg) (entry))) (4)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_5_priority_enabled := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) (PreH8 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_2) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 40)
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) (PreH8 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (entry_2) (after_2)) )
  **  (closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (0) (40)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_6 := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (0) (16)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_7 := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (0) (16)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_return_wit_8 := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (perr_pre <> 0)) (PreH7 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 42)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  EX (after: UCOS2_Verify_State)  (errv: Z)  (retv: Z) ,
  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (retv)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (retv) (errv)) )
  **  ((perr_pre) # UChar  |-> errv)
  **  (closed platform critical sg invocation origin mask after )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (perr_pre <> 0)) (PreH7 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (prio_pre = prio_in) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (publication_result_prop (critical) (sg) (invocation) (prio_in) (before) (after) (0) (42)) )
  **  (closed platform critical sg invocation origin mask after )
).

Definition OSMutexCreate_partial_solve_wit_1 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = prio_in)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (perr_pre <> 0)) (PreH6 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_2 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (perr_pre <> 0)) (PreH7 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_3 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((intNesting ((before.(IntrState) ))) > 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_4 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) > 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((intNesting ((before.(IntrState) ))) > 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_5 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_6 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_7_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 63) ”
.

Definition OSMutexCreate_partial_solve_wit_7_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 63) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_7_priority_enabled := OSMutexCreate_partial_solve_wit_7_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_7_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_8_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (prio_in = 255) ”
.

Definition OSMutexCreate_partial_solve_wit_8_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (prio_in = 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMutexCreate_partial_solve_wit_8_priority_disabled := OSMutexCreate_partial_solve_wit_8_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_8_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_9_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_10_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_11_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_12_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_13_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
.

Definition OSMutexCreate_partial_solve_wit_13_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (perr_pre <> 0)) (PreH9 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_13_priority_disabled := OSMutexCreate_partial_solve_wit_13_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_13_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_14_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
.

Definition OSMutexCreate_partial_solve_wit_14_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH2 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (perr_pre <> 0)) (PreH10 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_14_priority_enabled := OSMutexCreate_partial_solve_wit_14_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_14_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_15_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (perr_pre <> 0)) (PreH14 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_partial_solve_wit_15_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (perr_pre <> 0)) (PreH14 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_15_priority_enabled := OSMutexCreate_partial_solve_wit_15_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_15_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_16_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : (prio_pre <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH15 : (prio_pre < 63)) (PreH16 : (prio_pre <> 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (perr_pre <> 0)) (PreH21 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) <> 0) ”
.

Definition OSMutexCreate_partial_solve_wit_16_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : (prio_pre <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH15 : (prio_pre < 63)) (PreH16 : (prio_pre <> 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (perr_pre <> 0)) (PreH21 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) <> 0) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_16_priority_enabled := OSMutexCreate_partial_solve_wit_16_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_16_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_17_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) (PreH8 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ”
.

Definition OSMutexCreate_partial_solve_wit_17_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) (PreH8 : ((priority_value (sg) (entry) (prio_in)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry_2) (prio_in)) <> 0) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_17_priority_enabled := OSMutexCreate_partial_solve_wit_17_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_17_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_18_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : (prio_pre <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH15 : (prio_pre < 63)) (PreH16 : (prio_pre <> 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (perr_pre <> 0)) (PreH21 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ”
.

Definition OSMutexCreate_partial_solve_wit_18_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : (prio_pre <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH15 : (prio_pre < 63)) (PreH16 : (prio_pre <> 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (perr_pre <> 0)) (PreH21 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_18_priority_enabled := OSMutexCreate_partial_solve_wit_18_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_18_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_19_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (perr_pre <> 0)) (PreH13 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
.

Definition OSMutexCreate_partial_solve_wit_19_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (perr_pre <> 0)) (PreH13 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_19_priority_disabled := OSMutexCreate_partial_solve_wit_19_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_19_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_20_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : ((free_head (sg) (entry)) = 0)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (prio_in <> 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in < 64)) (PreH9 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : (prio_pre <> 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre < 63)) (PreH24 : (prio_pre <> 255)) (PreH25 : (prio_pre = prio_in)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : (perr_pre <> 0)) (PreH29 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
.

Definition OSMutexCreate_partial_solve_wit_20_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : ((free_head (sg) (entry)) = 0)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (prio_in <> 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in < 64)) (PreH9 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : (prio_pre <> 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre < 63)) (PreH24 : (prio_pre <> 255)) (PreH25 : (prio_pre = prio_in)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : (perr_pre <> 0)) (PreH29 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry_2) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_20_priority_enabled := OSMutexCreate_partial_solve_wit_20_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_20_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_21_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry)) = 0)) (PreH8 : (prio_pre <> 255)) (PreH9 : ((free_head (sg) (entry_3)) = 0)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (prio_in <> 255)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in < 64)) (PreH23 : (prio_pre <> 255)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH28 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH30 : (prio_pre < 63)) (PreH31 : (prio_pre <> 255)) (PreH32 : (prio_pre = prio_in)) (PreH33 : (0 <= prio_in)) (PreH34 : (prio_in <= 255)) (PreH35 : (perr_pre <> 0)) (PreH36 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
.

Definition OSMutexCreate_partial_solve_wit_21_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry)) = 0)) (PreH8 : (prio_pre <> 255)) (PreH9 : ((free_head (sg) (entry_3)) = 0)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (prio_in <> 255)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in < 64)) (PreH23 : (prio_pre <> 255)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH28 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH30 : (prio_pre < 63)) (PreH31 : (prio_pre <> 255)) (PreH32 : (prio_pre = prio_in)) (PreH33 : (0 <= prio_in)) (PreH34 : (prio_in <= 255)) (PreH35 : (perr_pre <> 0)) (PreH36 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ ((free_head (sg) (entry_3)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry_2) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_21_priority_enabled := OSMutexCreate_partial_solve_wit_21_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_21_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_22_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : ((free_head (sg) (entry)) = 0)) (PreH3 : (prio_in = 255)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (prio_pre = prio_in)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (perr_pre <> 0)) (PreH19 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
.

Definition OSMutexCreate_partial_solve_wit_22_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : ((free_head (sg) (entry)) = 0)) (PreH3 : (prio_in = 255)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (prio_pre = prio_in)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (perr_pre <> 0)) (PreH19 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_22_priority_disabled := OSMutexCreate_partial_solve_wit_22_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_22_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_23_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((free_head (sg) (entry)) = 0)) (PreH6 : (prio_pre = 255)) (PreH7 : ((free_head (sg) (entry_2)) = 0)) (PreH8 : (prio_in = 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (perr_pre <> 0)) (PreH24 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
.

Definition OSMutexCreate_partial_solve_wit_23_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((free_head (sg) (entry)) = 0)) (PreH6 : (prio_pre = 255)) (PreH7 : ((free_head (sg) (entry_2)) = 0)) (PreH8 : (prio_in = 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (perr_pre <> 0)) (PreH24 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ ((free_head (sg) (entry_2)) = 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_23_priority_disabled := OSMutexCreate_partial_solve_wit_23_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_23_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_24_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry)) = 0)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : ((free_head (sg) (entry_4)) = 0)) (PreH15 : (prio_pre <> 255)) (PreH16 : ((free_head (sg) (entry_3)) = 0)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (prio_in <> 255)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in < 64)) (PreH23 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (prio_in <> 255)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in < 64)) (PreH30 : (prio_pre <> 255)) (PreH31 : (0 <= prio_in)) (PreH32 : (prio_in <= 255)) (PreH33 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH34 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH35 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH36 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH37 : (prio_pre < 63)) (PreH38 : (prio_pre <> 255)) (PreH39 : (prio_pre = prio_in)) (PreH40 : (0 <= prio_in)) (PreH41 : (prio_in <= 255)) (PreH42 : (perr_pre <> 0)) (PreH43 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
.

Definition OSMutexCreate_partial_solve_wit_24_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry)) = 0)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : ((free_head (sg) (entry_4)) = 0)) (PreH15 : (prio_pre <> 255)) (PreH16 : ((free_head (sg) (entry_3)) = 0)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (prio_in <> 255)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in < 64)) (PreH23 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (prio_in <> 255)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in < 64)) (PreH30 : (prio_pre <> 255)) (PreH31 : (0 <= prio_in)) (PreH32 : (prio_in <= 255)) (PreH33 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH34 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH35 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH36 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH37 : (prio_pre < 63)) (PreH38 : (prio_pre <> 255)) (PreH39 : (prio_pre = prio_in)) (PreH40 : (0 <= prio_in)) (PreH41 : (prio_in <= 255)) (PreH42 : (perr_pre <> 0)) (PreH43 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry_4)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ ((free_head (sg) (entry_3)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry_2) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_24_priority_enabled := OSMutexCreate_partial_solve_wit_24_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_24_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_25_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry_5: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_5)) = 0)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH8 : (prio_in <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in < 64)) (PreH11 : ((free_head (sg) (entry_4)) = 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((free_head (sg) (entry_3)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : ((free_head (sg) (entry_2)) = 0)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in <= 255)) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH31 : (prio_in <> 255)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in < 64)) (PreH34 : (prio_pre <> 255)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH38 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH39 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH40 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH41 : (prio_pre < 63)) (PreH42 : (prio_pre <> 255)) (PreH43 : (prio_pre = prio_in)) (PreH44 : (0 <= prio_in)) (PreH45 : (prio_in <= 255)) (PreH46 : (perr_pre <> 0)) (PreH47 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_5 )
  **  (UCOS2_inv sg entry_5 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ”
.

Definition OSMutexCreate_partial_solve_wit_25_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (entry_5: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_5)) = 0)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH8 : (prio_in <> 255)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in < 64)) (PreH11 : ((free_head (sg) (entry_4)) = 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((free_head (sg) (entry_3)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : ((free_head (sg) (entry_2)) = 0)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH28 : (0 <= prio_in)) (PreH29 : (prio_in <= 255)) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH31 : (prio_in <> 255)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in < 64)) (PreH34 : (prio_pre <> 255)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH38 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH39 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH40 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH41 : (prio_pre < 63)) (PreH42 : (prio_pre <> 255)) (PreH43 : (prio_pre = prio_in)) (PreH44 : (0 <= prio_in)) (PreH45 : (prio_in <= 255)) (PreH46 : (perr_pre <> 0)) (PreH47 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_5 )
  **  (UCOS2_inv sg entry_5 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_5)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry_4)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry_3)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ ((free_head (sg) (entry_2)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_5 )
  **  (UCOS2_inv sg entry_5 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_25_priority_enabled := OSMutexCreate_partial_solve_wit_25_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_25_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_26_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_3)) = 0)) (PreH5 : (prio_in = 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = 0)) (PreH10 : (prio_pre = 255)) (PreH11 : ((free_head (sg) (entry)) = 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg entry_3 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ”
.

Definition OSMutexCreate_partial_solve_wit_26_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_3)) = 0)) (PreH5 : (prio_in = 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = 0)) (PreH10 : (prio_pre = 255)) (PreH11 : ((free_head (sg) (entry)) = 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg entry_3 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_3)) = 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_2)) = 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg entry_3 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_26_priority_disabled := OSMutexCreate_partial_solve_wit_26_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_26_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_27_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((free_head (sg) (entry)) <> 0)) (PreH2 : (prio_in = 255)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (prio_pre = 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre = prio_in)) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : (perr_pre <> 0)) (PreH18 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry))) ”
.

Definition OSMutexCreate_partial_solve_wit_27_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (PreH1 : ((free_head (sg) (entry)) <> 0)) (PreH2 : (prio_in = 255)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (prio_pre = 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH11 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre = prio_in)) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : (perr_pre <> 0)) (PreH18 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_27_priority_disabled := OSMutexCreate_partial_solve_wit_27_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_27_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_28_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : ((free_head (sg) (entry)) <> 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry))) ”
.

Definition OSMutexCreate_partial_solve_wit_28_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (PreH1 : ((free_head (sg) (entry)) <> 0)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : (prio_in <> 255)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in < 64)) (PreH8 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : (prio_pre <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry_2) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_28_priority_enabled := OSMutexCreate_partial_solve_wit_28_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_28_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_29_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH5 : ((free_head (sg) (entry_2)) <> 0)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : (prio_in <> 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in < 64)) (PreH12 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_in <> 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in < 64)) (PreH19 : (prio_pre <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH26 : (prio_pre < 63)) (PreH27 : (prio_pre <> 255)) (PreH28 : (prio_pre = prio_in)) (PreH29 : (0 <= prio_in)) (PreH30 : (prio_in <= 255)) (PreH31 : (perr_pre <> 0)) (PreH32 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3))) ” 
  &&  “ ((free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  ((&(((free_head (sg) (entry_3)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_30_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH5 : ((free_head (sg) (entry)) <> 0)) (PreH6 : (prio_in = 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : (prio_pre = 255)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (perr_pre <> 0)) (PreH22 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry_2))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_31_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH5 : ((free_head (sg) (entry)) <> 0)) (PreH6 : (prio_in = 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : (prio_pre = 255)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (perr_pre <> 0)) (PreH22 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
.

Definition OSMutexCreate_partial_solve_wit_31_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_2: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH5 : ((free_head (sg) (entry)) <> 0)) (PreH6 : (prio_in = 255)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : (prio_pre = 255)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (perr_pre <> 0)) (PreH22 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry_2))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_31_priority_disabled := OSMutexCreate_partial_solve_wit_31_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_31_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_32_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH5 : ((free_head (sg) (entry_2)) <> 0)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : (prio_in <> 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in < 64)) (PreH12 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_in <> 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in < 64)) (PreH19 : (prio_pre <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH26 : (prio_pre < 63)) (PreH27 : (prio_pre <> 255)) (PreH28 : (prio_pre = prio_in)) (PreH29 : (0 <= prio_in)) (PreH30 : (prio_in <= 255)) (PreH31 : (perr_pre <> 0)) (PreH32 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((&(((free_head (sg) (entry_3)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
.

Definition OSMutexCreate_partial_solve_wit_32_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH5 : ((free_head (sg) (entry_2)) <> 0)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : (prio_in <> 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in < 64)) (PreH12 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_in <> 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in < 64)) (PreH19 : (prio_pre <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH23 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH24 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH26 : (prio_pre < 63)) (PreH27 : (prio_pre <> 255)) (PreH28 : (prio_pre = prio_in)) (PreH29 : (0 <= prio_in)) (PreH30 : (prio_in <= 255)) (PreH31 : (perr_pre <> 0)) (PreH32 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((&(((free_head (sg) (entry_3)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3))) ” 
  &&  “ ((free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_32_priority_enabled := OSMutexCreate_partial_solve_wit_32_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_32_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_33_priority_enabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3))) ” 
  &&  “ ((free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_34_priority_disabled := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH8 : ((free_head (sg) (entry)) <> 0)) (PreH9 : (prio_in = 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in <= 255)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH18 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (perr_pre <> 0)) (PreH25 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry_2))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (event_wait_list_init_pre &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_35_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH8 : ((free_head (sg) (entry)) <> 0)) (PreH9 : (prio_in = 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in <= 255)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH18 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (perr_pre <> 0)) (PreH25 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (event_wait_list_init_post &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
.

Definition OSMutexCreate_partial_solve_wit_35_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH8 : ((free_head (sg) (entry)) <> 0)) (PreH9 : (prio_in = 255)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in <= 255)) (PreH16 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH17 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH18 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (perr_pre <> 0)) (PreH25 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (event_wait_list_init_post &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry_2))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_post &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_35_priority_disabled := OSMutexCreate_partial_solve_wit_35_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_35_priority_disabled_aux.

Definition OSMutexCreate_partial_solve_wit_36_priority_enabled_pure := 
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255) = ((prio_pre * 256 ) + 255 )) ”
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH10 : ((free_head (sg) (entry_2)) <> 0)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH14 : (prio_in <> 255)) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in < 64)) (PreH17 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (prio_in <> 255)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in < 64)) (PreH24 : (prio_pre <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH31 : (prio_pre < 63)) (PreH32 : (prio_pre <> 255)) (PreH33 : (prio_pre = prio_in)) (PreH34 : (0 <= prio_in)) (PreH35 : (prio_in <= 255)) (PreH36 : (perr_pre <> 0)) (PreH37 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255) = ((prio_pre * 256 ) + 255 )) ”
).

Definition OSMutexCreate_partial_solve_wit_36_priority_enabled_pure_split_goal_1 := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH9 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH10 : ((free_head (sg) (entry_2)) <> 0)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH14 : (prio_in <> 255)) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in < 64)) (PreH17 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (prio_in <> 255)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in < 64)) (PreH24 : (prio_pre <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH30 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH31 : (prio_pre < 63)) (PreH32 : (prio_pre <> 255)) (PreH33 : (prio_pre = prio_in)) (PreH34 : (0 <= prio_in)) (PreH35 : (prio_in <= 255)) (PreH36 : (perr_pre <> 0)) (PreH37 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255) = ((prio_pre * 256 ) + 255 )) ”
.

Definition OSMutexCreate_partial_solve_wit_36_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH8 : ((free_head (sg) (entry_2)) <> 0)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH19 : (prio_in <> 255)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in < 64)) (PreH22 : (prio_pre <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH26 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH27 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH29 : (prio_pre < 63)) (PreH30 : (prio_pre <> 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (perr_pre <> 0)) (PreH35 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255) = ((prio_pre * 256 ) + 255 )) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3))) ” 
  &&  “ ((free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_36_priority_enabled := OSMutexCreate_partial_solve_wit_36_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_36_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_37_priority_enabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH11 : ((free_head (sg) (entry_2)) <> 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : (prio_pre <> 255)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH30 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH31 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (perr_pre <> 0)) (PreH38 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ”
.

Definition OSMutexCreate_partial_solve_wit_37_priority_enabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (entry_3: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_4: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3)))) (PreH11 : ((free_head (sg) (entry_2)) <> 0)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in <= 255)) (PreH14 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((priority_value (sg) (entry) (prio_in)) = 0)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : (prio_pre <> 255)) (PreH26 : (0 <= prio_in)) (PreH27 : (prio_in <= 255)) (PreH28 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH29 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH30 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH31 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (perr_pre <> 0)) (PreH38 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry_3))) ” 
  &&  “ ((free_head (sg) (entry_2)) <> 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) = 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_37_priority_enabled := OSMutexCreate_partial_solve_wit_37_priority_enabled_pure -> OSMutexCreate_partial_solve_wit_37_priority_enabled_aux.

Definition OSMutexCreate_partial_solve_wit_38_priority_disabled_pure := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_3)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ”
.

Definition OSMutexCreate_partial_solve_wit_38_priority_disabled_aux := 
forall (perr_pre: Z) (prio_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (perr_in: Z) (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (entry_2: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (entry_3: UCOS2_Verify_State) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH10 : ((free_head (sg) (entry)) = (free_head (sg) (entry_2)))) (PreH11 : ((free_head (sg) (entry)) <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH20 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH21 : (0 <= (intNesting ((before.(IntrState) ))))) (PreH22 : ((intNesting ((before.(IntrState) ))) <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (perr_pre <> 0)) (PreH28 : (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X )) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_3)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (retval = retval) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = (free_head (sg) (entry_2))) ” 
  &&  “ ((free_head (sg) (entry)) <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (safeExec (LastSeen (before)) (atomic_cmd ((publication_call_program (critical) (sg) (invocation) (prio_in)))) X ) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (255) (eid) (rest) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSMutexCreate_partial_solve_wit_38_priority_disabled := OSMutexCreate_partial_solve_wit_38_priority_disabled_pure -> OSMutexCreate_partial_solve_wit_38_priority_disabled_aux.

Definition OSMutexCreate_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
|--
  “ (0 <= (intNesting ((before.(IntrState) )))) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 255) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
|--
  “ ((intNesting ((before.(IntrState) ))) <= 255) ” 
  &&  “ (0 <= (intNesting ((before.(IntrState) )))) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
).

Definition OSMutexCreate_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
|--
  “ ((intNesting ((before.(IntrState) ))) <= 255) ”
.

Definition OSMutexCreate_which_implies_wit_1_split_goal_2 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
|--
  “ (0 <= (intNesting ((before.(IntrState) )))) ”
.

Definition OSMutexCreate_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
.

Definition OSMutexCreate_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
).

Definition OSMutexCreate_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
.

Definition OSMutexCreate_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
).

Definition OSMutexCreate_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
|--
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
.

Definition OSMutexCreate_which_implies_wit_4 := 
(
forall (prio_in: Z) (sg: StableGlobVars) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 63)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
) \/
(
forall (prio_in: Z) (sg: StableGlobVars) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 63)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
).

Definition OSMutexCreate_which_implies_wit_4_split_goal_spatial := 
forall (prio_in: Z) (sg: StableGlobVars) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 63)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
.

Definition OSMutexCreate_which_implies_wit_5 := 
(
forall (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
) \/
(
forall (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
).

Definition OSMutexCreate_which_implies_wit_5_split_goal_spatial := 
forall (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
.

Definition OSMutexCreate_which_implies_wit_6 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  (closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  (closed platform critical sg invocation origin mask before )
).

Definition OSMutexCreate_which_implies_wit_6_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  (closed platform critical sg invocation origin mask before )
.

Definition OSMutexCreate_which_implies_wit_7 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
).

Definition OSMutexCreate_which_implies_wit_8 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (priority_table sg entry_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (priority_table sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
).

Definition OSMutexCreate_which_implies_wit_9 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry_2) (prio_in)))
  **  (priority_table_missing sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) <> 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) <> 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry_2) (prio_in)))
  **  (priority_table_missing sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((priority_value (sg) (entry) (prio_in)) <> 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
).

Definition OSMutexCreate_which_implies_wit_10 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((priority_value (sg) (entry_2) (prio_in)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry_2 prio_in )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
).

Definition OSMutexCreate_which_implies_wit_11 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (priority_table sg entry_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (priority_table sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
).

Definition OSMutexCreate_which_implies_wit_12 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (reserved_priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (reserved_priority_table_missing sg entry prio_in )
).

Definition OSMutexCreate_which_implies_wit_13 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : (prio_in <> 255)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in < 64)) (PreH7 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry_2 prio_in )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
).

Definition OSMutexCreate_which_implies_wit_14 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (prio_in = 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH5 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
).

Definition OSMutexCreate_which_implies_wit_15 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (priority_table sg entry_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) = 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (priority_table sg entry_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ ((free_head (sg) (entry)) = 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
).

Definition OSMutexCreate_which_implies_wit_16 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (pevent: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) <> 0)) (PreH5 : (pevent = (free_head (sg) (entry_2)))) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (pevent = (free_head (sg) (entry))) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (node_residual sg entry eid )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false pevent image EventPtrField )
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (pevent: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) (PreH4 : ((free_head (sg) (entry_2)) <> 0)) (PreH5 : (pevent = (free_head (sg) (entry_2)))) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (head_residual sg entry_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (entry: UCOS2_Verify_State) ,
  “ ((free_head (sg) (entry_2)) = (free_head (sg) (entry))) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ” 
  &&  “ (pevent = (free_head (sg) (entry))) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (node_residual sg entry eid )
  **  (reserved_priority_table sg entry prio_in )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false pevent image EventPtrField )
).

Definition OSMutexCreate_which_implies_wit_17 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (image_2: EventStorage) (rest_2: (@list Z)) (eid_2: Z) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (pevent: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid_2) (rest_2) (image_2)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid_2)) )
  **  (coq_prop (event_pointer_eq (sg) (eid_2) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (node_residual sg entry_2 eid_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest_2)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest_2)))))
  **  (event_storage_without_field false pevent image_2 EventPtrField )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (node_residual sg entry eid )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding pevent image )
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (image_2: EventStorage) (rest_2: (@list Z)) (eid_2: Z) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (pevent: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid_2) (rest_2) (image_2)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid_2)) )
  **  (coq_prop (event_pointer_eq (sg) (eid_2) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (node_residual sg entry_2 eid_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  (event_storage_without_field false pevent image_2 EventPtrField )
|--
  EX (x_2: Z)  (x: Z)  (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (entry: UCOS2_Verify_State) ,
  “ ((event_encode_pool_link (sg) ((hd_error (rest_2)))) = (event_encode_pool_link (sg) ((hd_error (rest))))) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> x_2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> x)
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (node_residual sg entry eid )
  **  (reserved_priority_table sg entry prio_in )
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding pevent image )
).

Definition OSMutexCreate_which_implies_wit_18 := 
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (image_2: EventStorage) (rest_2: (@list Z)) (eid_2: Z) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (pevent: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid_2) (rest_2) (image_2)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid_2)) )
  **  (coq_prop (event_pointer_eq (sg) (eid_2) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (node_residual sg entry_2 eid_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest_2)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding pevent image_2 )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) (pevent)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry)) )
) \/
(
forall (prio_in: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (image_2: EventStorage) (rest_2: (@list Z)) (eid_2: Z) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (pevent: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in <= 255)) (PreH3 : ((intNesting ((before.(IntrState) ))) <= 0)) ,
  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid_2) (rest_2) (image_2)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid_2)) )
  **  (coq_prop (event_pointer_eq (sg) (eid_2) (pevent)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (node_residual sg entry_2 eid_2 )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest_2)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding pevent image_2 )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ ((intNesting ((before.(IntrState) ))) <= 0) ”
  &&  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (cpu_sr) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) (pevent)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry)) )
).

Module Type VC_Correct.


Axiom proof_of_OSMutexCreate_safety_wit_1 : OSMutexCreate_safety_wit_1.
Axiom proof_of_OSMutexCreate_safety_wit_2 : OSMutexCreate_safety_wit_2.
Axiom proof_of_OSMutexCreate_safety_wit_3 : OSMutexCreate_safety_wit_3.
Axiom proof_of_OSMutexCreate_safety_wit_4_priority_enabled : OSMutexCreate_safety_wit_4_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_5_priority_disabled : OSMutexCreate_safety_wit_5_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_6_priority_enabled : OSMutexCreate_safety_wit_6_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_7_priority_disabled : OSMutexCreate_safety_wit_7_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_8_priority_enabled : OSMutexCreate_safety_wit_8_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_9_priority_enabled : OSMutexCreate_safety_wit_9_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_10_priority_enabled : OSMutexCreate_safety_wit_10_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_11_priority_enabled : OSMutexCreate_safety_wit_11_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_12_priority_enabled : OSMutexCreate_safety_wit_12_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_13_priority_disabled : OSMutexCreate_safety_wit_13_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_14_priority_enabled : OSMutexCreate_safety_wit_14_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_15_priority_disabled : OSMutexCreate_safety_wit_15_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_16_priority_enabled : OSMutexCreate_safety_wit_16_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_17_priority_enabled : OSMutexCreate_safety_wit_17_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_18_priority_disabled : OSMutexCreate_safety_wit_18_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_19_priority_enabled : OSMutexCreate_safety_wit_19_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_20_priority_disabled : OSMutexCreate_safety_wit_20_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_21_priority_enabled : OSMutexCreate_safety_wit_21_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_22_priority_disabled : OSMutexCreate_safety_wit_22_priority_disabled.
Axiom proof_of_OSMutexCreate_safety_wit_23_priority_enabled : OSMutexCreate_safety_wit_23_priority_enabled.
Axiom proof_of_OSMutexCreate_safety_wit_24_priority_disabled : OSMutexCreate_safety_wit_24_priority_disabled.
Axiom proof_of_OSMutexCreate_return_wit_1_priority_enabled : OSMutexCreate_return_wit_1_priority_enabled.
Axiom proof_of_OSMutexCreate_return_wit_2_priority_disabled : OSMutexCreate_return_wit_2_priority_disabled.
Axiom proof_of_OSMutexCreate_return_wit_3_priority_enabled : OSMutexCreate_return_wit_3_priority_enabled.
Axiom proof_of_OSMutexCreate_return_wit_4_priority_disabled : OSMutexCreate_return_wit_4_priority_disabled.
Axiom proof_of_OSMutexCreate_return_wit_5_priority_enabled : OSMutexCreate_return_wit_5_priority_enabled.
Axiom proof_of_OSMutexCreate_return_wit_6 : OSMutexCreate_return_wit_6.
Axiom proof_of_OSMutexCreate_return_wit_7 : OSMutexCreate_return_wit_7.
Axiom proof_of_OSMutexCreate_return_wit_8 : OSMutexCreate_return_wit_8.
Axiom proof_of_OSMutexCreate_partial_solve_wit_1 : OSMutexCreate_partial_solve_wit_1.
Axiom proof_of_OSMutexCreate_partial_solve_wit_2 : OSMutexCreate_partial_solve_wit_2.
Axiom proof_of_OSMutexCreate_partial_solve_wit_3 : OSMutexCreate_partial_solve_wit_3.
Axiom proof_of_OSMutexCreate_partial_solve_wit_4 : OSMutexCreate_partial_solve_wit_4.
Axiom proof_of_OSMutexCreate_partial_solve_wit_5 : OSMutexCreate_partial_solve_wit_5.
Axiom proof_of_OSMutexCreate_partial_solve_wit_6 : OSMutexCreate_partial_solve_wit_6.
Axiom proof_of_OSMutexCreate_partial_solve_wit_7_priority_enabled_pure : OSMutexCreate_partial_solve_wit_7_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_7_priority_enabled : OSMutexCreate_partial_solve_wit_7_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_8_priority_disabled_pure : OSMutexCreate_partial_solve_wit_8_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_8_priority_disabled : OSMutexCreate_partial_solve_wit_8_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_9_priority_disabled : OSMutexCreate_partial_solve_wit_9_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_10_priority_enabled : OSMutexCreate_partial_solve_wit_10_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_11_priority_enabled : OSMutexCreate_partial_solve_wit_11_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_12_priority_disabled : OSMutexCreate_partial_solve_wit_12_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_13_priority_disabled_pure : OSMutexCreate_partial_solve_wit_13_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_13_priority_disabled : OSMutexCreate_partial_solve_wit_13_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_14_priority_enabled_pure : OSMutexCreate_partial_solve_wit_14_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_14_priority_enabled : OSMutexCreate_partial_solve_wit_14_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_15_priority_enabled_pure : OSMutexCreate_partial_solve_wit_15_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_15_priority_enabled : OSMutexCreate_partial_solve_wit_15_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_16_priority_enabled_pure : OSMutexCreate_partial_solve_wit_16_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_16_priority_enabled : OSMutexCreate_partial_solve_wit_16_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_17_priority_enabled_pure : OSMutexCreate_partial_solve_wit_17_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_17_priority_enabled : OSMutexCreate_partial_solve_wit_17_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_18_priority_enabled_pure : OSMutexCreate_partial_solve_wit_18_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_18_priority_enabled : OSMutexCreate_partial_solve_wit_18_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_19_priority_disabled_pure : OSMutexCreate_partial_solve_wit_19_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_19_priority_disabled : OSMutexCreate_partial_solve_wit_19_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_20_priority_enabled_pure : OSMutexCreate_partial_solve_wit_20_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_20_priority_enabled : OSMutexCreate_partial_solve_wit_20_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_21_priority_enabled_pure : OSMutexCreate_partial_solve_wit_21_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_21_priority_enabled : OSMutexCreate_partial_solve_wit_21_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_22_priority_disabled_pure : OSMutexCreate_partial_solve_wit_22_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_22_priority_disabled : OSMutexCreate_partial_solve_wit_22_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_23_priority_disabled_pure : OSMutexCreate_partial_solve_wit_23_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_23_priority_disabled : OSMutexCreate_partial_solve_wit_23_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_24_priority_enabled_pure : OSMutexCreate_partial_solve_wit_24_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_24_priority_enabled : OSMutexCreate_partial_solve_wit_24_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_25_priority_enabled_pure : OSMutexCreate_partial_solve_wit_25_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_25_priority_enabled : OSMutexCreate_partial_solve_wit_25_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_26_priority_disabled_pure : OSMutexCreate_partial_solve_wit_26_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_26_priority_disabled : OSMutexCreate_partial_solve_wit_26_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_27_priority_disabled_pure : OSMutexCreate_partial_solve_wit_27_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_27_priority_disabled : OSMutexCreate_partial_solve_wit_27_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_28_priority_enabled_pure : OSMutexCreate_partial_solve_wit_28_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_28_priority_enabled : OSMutexCreate_partial_solve_wit_28_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_29_priority_enabled : OSMutexCreate_partial_solve_wit_29_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_30_priority_disabled : OSMutexCreate_partial_solve_wit_30_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_31_priority_disabled_pure : OSMutexCreate_partial_solve_wit_31_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_31_priority_disabled : OSMutexCreate_partial_solve_wit_31_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_32_priority_enabled_pure : OSMutexCreate_partial_solve_wit_32_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_32_priority_enabled : OSMutexCreate_partial_solve_wit_32_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_33_priority_enabled : OSMutexCreate_partial_solve_wit_33_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_34_priority_disabled : OSMutexCreate_partial_solve_wit_34_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_35_priority_disabled_pure : OSMutexCreate_partial_solve_wit_35_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_35_priority_disabled : OSMutexCreate_partial_solve_wit_35_priority_disabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_36_priority_enabled_pure : OSMutexCreate_partial_solve_wit_36_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_36_priority_enabled : OSMutexCreate_partial_solve_wit_36_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_37_priority_enabled_pure : OSMutexCreate_partial_solve_wit_37_priority_enabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_37_priority_enabled : OSMutexCreate_partial_solve_wit_37_priority_enabled.
Axiom proof_of_OSMutexCreate_partial_solve_wit_38_priority_disabled_pure : OSMutexCreate_partial_solve_wit_38_priority_disabled_pure.
Axiom proof_of_OSMutexCreate_partial_solve_wit_38_priority_disabled : OSMutexCreate_partial_solve_wit_38_priority_disabled.
Axiom proof_of_OSMutexCreate_which_implies_wit_1 : OSMutexCreate_which_implies_wit_1.
Axiom proof_of_OSMutexCreate_which_implies_wit_2 : OSMutexCreate_which_implies_wit_2.
Axiom proof_of_OSMutexCreate_which_implies_wit_3 : OSMutexCreate_which_implies_wit_3.
Axiom proof_of_OSMutexCreate_which_implies_wit_4 : OSMutexCreate_which_implies_wit_4.
Axiom proof_of_OSMutexCreate_which_implies_wit_5 : OSMutexCreate_which_implies_wit_5.
Axiom proof_of_OSMutexCreate_which_implies_wit_6 : OSMutexCreate_which_implies_wit_6.
Axiom proof_of_OSMutexCreate_which_implies_wit_7 : OSMutexCreate_which_implies_wit_7.
Axiom proof_of_OSMutexCreate_which_implies_wit_8 : OSMutexCreate_which_implies_wit_8.
Axiom proof_of_OSMutexCreate_which_implies_wit_9 : OSMutexCreate_which_implies_wit_9.
Axiom proof_of_OSMutexCreate_which_implies_wit_10 : OSMutexCreate_which_implies_wit_10.
Axiom proof_of_OSMutexCreate_which_implies_wit_11 : OSMutexCreate_which_implies_wit_11.
Axiom proof_of_OSMutexCreate_which_implies_wit_12 : OSMutexCreate_which_implies_wit_12.
Axiom proof_of_OSMutexCreate_which_implies_wit_13 : OSMutexCreate_which_implies_wit_13.
Axiom proof_of_OSMutexCreate_which_implies_wit_14 : OSMutexCreate_which_implies_wit_14.
Axiom proof_of_OSMutexCreate_which_implies_wit_15 : OSMutexCreate_which_implies_wit_15.
Axiom proof_of_OSMutexCreate_which_implies_wit_16 : OSMutexCreate_which_implies_wit_16.
Axiom proof_of_OSMutexCreate_which_implies_wit_17 : OSMutexCreate_which_implies_wit_17.
Axiom proof_of_OSMutexCreate_which_implies_wit_18 : OSMutexCreate_which_implies_wit_18.

End VC_Correct.
