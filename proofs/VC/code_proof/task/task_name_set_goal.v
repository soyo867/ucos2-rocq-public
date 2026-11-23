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
Require Import Ucos2Verify.VC.code.task.spec.task_name_set_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskNameSet -----*)

Definition OSTaskNameSet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <= 63)) (PreH2 : (prio_pre = request)) (PreH3 : (pname_pre = name)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (0 <= request)) (PreH6 : (request <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre > 63)) (PreH9 : (prio_pre = request)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre <= 63)) (PreH8 : (prio_pre = request)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (0 <= request)) (PreH12 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) (PreH3 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_7 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 0)) (PreH2 : (0 <= prio)) (PreH3 : (prio <= 63)) (PreH4 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskNameSet_safety_wit_8 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_safety_wit_9 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameSet_entail_wit_1_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre > 63)) (PreH9 : (prio_pre = request)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (acquired: UCOS2_Verify_State) ,
  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (retval) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre > 63)) (PreH9 : (prio_pre = request)) (PreH10 : (pname_pre = name)) (PreH11 : (perr_pre = error_addr)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (x: Z)  (acquired: UCOS2_Verify_State) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (prio_pre = request) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (retval) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_1_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre <= 63)) (PreH8 : (prio_pre = request)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (0 <= request)) (PreH12 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (acquired: UCOS2_Verify_State) ,
  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (retval) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : ((task_name_set_nesting (before)) <= 0)) (PreH4 : (0 <= (task_name_set_nesting (before)))) (PreH5 : ((task_name_set_nesting (before)) <= 255)) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre <= 63)) (PreH8 : (prio_pre = request)) (PreH9 : (pname_pre = name)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (0 <= request)) (PreH12 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (x: Z)  (acquired: UCOS2_Verify_State) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (prio_pre = request) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (retval) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) = 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  EX (tid: Z)  (task: TaskAbstractState) ,
  “ (request = 255) ” 
  &&  “ (0 <= (curPrio (task))) ” 
  &&  “ ((curPrio (task)) <= 63) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_current (acquired) (tid) (task)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (task_name_set_self_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) = 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  EX (tid: Z)  (task: TaskAbstractState) ,
  “ (request = 255) ” 
  &&  “ (0 <= (curPrio (task))) ” 
  &&  “ ((curPrio (task)) <= 63) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_current (acquired) (tid) (task)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (task_name_set_self_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
).

Definition OSTaskNameSet_entail_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (tid: Z) (task: TaskAbstractState) (PreH1 : (request = 255)) (PreH2 : (0 <= (curPrio (task)))) (PreH3 : ((curPrio (task)) <= 63)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_current (acquired) (tid) (task)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (task_name_set_self_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= (curPrio (task))) ” 
  &&  “ ((curPrio (task)) <= 63) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) ((curPrio (task)))) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (tid: Z) (task: TaskAbstractState) (PreH1 : (request = 255)) (PreH2 : (0 <= (curPrio (task)))) (PreH3 : ((curPrio (task)) <= 63)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_current (acquired) (tid) (task)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (task_name_set_self_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
|--
  (coq_prop (task_name_set_resolved (request) (acquired) ((curPrio (task)))) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (tid: Z) (task: TaskAbstractState) (PreH1 : (request = 255)) (PreH2 : (0 <= (curPrio (task)))) (PreH3 : ((curPrio (task)) <= 63)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_current (acquired) (tid) (task)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (task_name_set_self_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
|--
  (coq_prop (task_name_set_resolved (request) (acquired) ((curPrio (task)))) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
.

Definition OSTaskNameSet_entail_wit_4_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
.

Definition OSTaskNameSet_entail_wit_4_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= request) ” 
  &&  “ (request <= 63) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) (request)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (request <= 63) ” 
  &&  “ (0 <= request) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) (request)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_4_2_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (request <= 63) ”
.

Definition OSTaskNameSet_entail_wit_4_2_split_goal_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (0 <= request) ”
.

Definition OSTaskNameSet_entail_wit_4_2_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  (coq_prop (task_name_set_resolved (request) (acquired) (request)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
.

Definition OSTaskNameSet_entail_wit_5 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_set_table_entry (sg) (acquired) (prio)))
  **  (task_name_set_table_frame sg acquired prio )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ ((task_name_set_table_entry (sg) (acquired) (prio)) = (task_name_set_table_entry (sg) (acquired) (prio))) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_set_table_entry (sg) (acquired) (prio)))
  **  (task_name_set_table_frame sg acquired prio )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
|--
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_5_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_set_table_entry (sg) (acquired) (prio)))
  **  (task_name_set_table_frame sg acquired prio )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
|--
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
.

Definition OSTaskNameSet_entail_wit_6 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= prio)) (PreH3 : (prio <= 63)) (PreH4 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= prio)) (PreH3 : (prio <= 63)) (PreH4 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_6_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= prio)) (PreH3 : (prio <= 63)) (PreH4 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
.

Definition OSTaskNameSet_entail_wit_7 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskNameSet_entail_wit_7_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
.

Definition OSTaskNameSet_entail_wit_8 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  EX (task: TaskAbstractState)  (tid: Z) ,
  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_target (acquired) (prio) (tid) (task)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (tcbTaskName (task)))
  **  (task_name_set_field_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_name_set_table_entry (sg) (acquired) (prio)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  EX (task: TaskAbstractState)  (tid: Z) ,
  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_target (acquired) (prio) (tid) (task)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (tcbTaskName (task)))
  **  (task_name_set_field_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
).

Definition OSTaskNameSet_entail_wit_9 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (ptcb: Z) (tid: Z) (task: TaskAbstractState) (PreH1 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_name_set_target (acquired) (prio) (tid) (task)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> name)
  **  (task_name_set_field_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((error_addr) # UChar  |->_)
|--
  EX (released: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (ptcb: Z) (tid: Z) (task: TaskAbstractState) (PreH1 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_target (acquired) (prio) (tid) (task)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> name)
  **  (task_name_set_field_frame sg acquired tid task )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
|--
  EX (released: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
).

Definition OSTaskNameSet_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((error_addr) # UChar  |-> 67)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (67) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((error_addr) # UChar  |-> 67)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (67) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (prio_pre = request)) (PreH8 : (pname_pre = name)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |-> 18)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (prio_pre = request)) (PreH8 : (pname_pre = name)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (18) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (prio_pre = request)) (PreH7 : (pname_pre = name)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |-> 18)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (prio_pre = request)) (PreH7 : (pname_pre = name)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (18) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (prio_pre = request)) (PreH5 : (pname_pre = name)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (prio_pre = request)) (PreH5 : (pname_pre = name)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (12) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_6 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (12) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_7 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 42)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (42) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_return_wit_8 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  ((error_addr) # UChar  |-> 0)
|--
  EX (err: Z)  (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (err) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
  **  ((error_addr) # UChar  |-> err)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (task_name_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_name_set_post (critical) (sg) (invocation) (request) (name) (before) (0) (current) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask current )
).

Definition OSTaskNameSet_partial_solve_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (task_name_set_closed platform critical sg invocation origin mask before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (prio_pre = request)) (PreH5 : (pname_pre = name)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (task_name_set_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (task_name_set_closed platform critical sg invocation origin mask before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (prio_pre = request)) (PreH4 : (pname_pre = name)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (prio_pre = request)) (PreH5 : (pname_pre = name)) (PreH6 : (perr_pre = error_addr)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (prio_pre = request)) (PreH7 : (pname_pre = name)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_set_nesting (before)) > 0) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) > 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (prio_pre = request)) (PreH8 : (pname_pre = name)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_set_nesting (before)) > 0) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (prio_pre = request)) (PreH7 : (pname_pre = name)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (prio_pre = request)) (PreH8 : (pname_pre = name)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (prio_pre = request)) (PreH8 : (pname_pre = name)) (PreH9 : (perr_pre = error_addr)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((task_name_set_nesting (before)) <= 0)) (PreH2 : (0 <= (task_name_set_nesting (before)))) (PreH3 : ((task_name_set_nesting (before)) <= 255)) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (prio_pre = request)) (PreH7 : (pname_pre = name)) (PreH8 : (perr_pre = error_addr)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_set_nesting (before)) <= 0) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (pname_pre = name) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_admission (critical) (sg) (invocation) (request) (name) (before)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_11_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ”
.

Definition OSTaskNameSet_partial_solve_wit_11_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ”
  &&  (UCOS2_inv sg acquired )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_layout (sg)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((error_addr) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_11 := OSTaskNameSet_partial_solve_wit_11_pure -> OSTaskNameSet_partial_solve_wit_11_aux.

Definition OSTaskNameSet_partial_solve_wit_12_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskNameSet_partial_solve_wit_12_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((error_addr) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_12 := OSTaskNameSet_partial_solve_wit_12_pure -> OSTaskNameSet_partial_solve_wit_12_aux.

Definition OSTaskNameSet_partial_solve_wit_13_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskNameSet_partial_solve_wit_13_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((error_addr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (67) (acquired)) )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  ((error_addr) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_13 := OSTaskNameSet_partial_solve_wit_13_pure -> OSTaskNameSet_partial_solve_wit_13_aux.

Definition OSTaskNameSet_partial_solve_wit_14_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  ((( &( "pname" ) )) # Ptr  |-> name)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((error_addr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskNameSet_partial_solve_wit_14_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (error_addr: Z) (name: Z) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) ,
  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  ((error_addr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  (coq_prop (task_name_set_resolved (request) (acquired) (prio)) )
  **  (coq_prop (task_name_set_safe (critical) (sg) (invocation) (request) (name) (before) (X)) )
  **  (coq_prop (task_name_set_context (critical) (sg) (invocation) (request) (name) (mask) (cpu_sr) (before) (acquired)) )
  **  (coq_prop (task_name_set_step (prio) (name) (acquired) (0) (released)) )
  **  ((error_addr) # UChar  |->_)
.

Definition OSTaskNameSet_partial_solve_wit_14 := OSTaskNameSet_partial_solve_wit_14_pure -> OSTaskNameSet_partial_solve_wit_14_aux.

Definition OSTaskNameSet_which_implies_wit_1 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_set_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_set_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSTaskNameSet_which_implies_wit_1_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_set_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSTaskNameSet_which_implies_wit_2 := 
(
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
|--
  “ (0 <= (task_name_set_nesting (before))) ” 
  &&  “ ((task_name_set_nesting (before)) <= 255) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
) \/
(
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
|--
  “ ((task_name_set_nesting (before)) <= 255) ” 
  &&  “ (0 <= (task_name_set_nesting (before))) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
).

Definition OSTaskNameSet_which_implies_wit_2_split_goal_1 := 
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
|--
  “ ((task_name_set_nesting (before)) <= 255) ”
.

Definition OSTaskNameSet_which_implies_wit_2_split_goal_2 := 
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
|--
  “ (0 <= (task_name_set_nesting (before))) ”
.

Definition OSTaskNameSet_which_implies_wit_2_split_goal_spatial := 
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
.

Definition OSTaskNameSet_which_implies_wit_3 := 
(
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSTaskNameSet_which_implies_wit_3_split_goal_spatial := 
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSTaskNameSet_which_implies_wit_4 := 
(
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSTaskNameSet_which_implies_wit_4_split_goal_spatial := 
forall (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) ,
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_set_nesting (before)))
  **  (task_name_set_observation_frame sg before )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSTaskNameSet_which_implies_wit_5 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) ,
  (UCOS2_inv sg acquired )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ”
  &&  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_set_table_entry (sg) (acquired) (prio)))
  **  (task_name_set_table_frame sg acquired prio )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) ,
  (UCOS2_inv sg acquired )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_set_table_entry (sg) (acquired) (prio)))
  **  (task_name_set_table_frame sg acquired prio )
).

Definition OSTaskNameSet_which_implies_wit_5_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (0 <= prio)) (PreH2 : (prio <= 63)) ,
  (UCOS2_inv sg acquired )
  **  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
|--
  (coq_prop (task_name_set_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_set_table_entry (sg) (acquired) (prio)))
  **  (task_name_set_table_frame sg acquired prio )
.

Module Type VC_Correct.


Axiom proof_of_OSTaskNameSet_safety_wit_1 : OSTaskNameSet_safety_wit_1.
Axiom proof_of_OSTaskNameSet_safety_wit_2 : OSTaskNameSet_safety_wit_2.
Axiom proof_of_OSTaskNameSet_safety_wit_3 : OSTaskNameSet_safety_wit_3.
Axiom proof_of_OSTaskNameSet_safety_wit_4 : OSTaskNameSet_safety_wit_4.
Axiom proof_of_OSTaskNameSet_safety_wit_5 : OSTaskNameSet_safety_wit_5.
Axiom proof_of_OSTaskNameSet_safety_wit_6 : OSTaskNameSet_safety_wit_6.
Axiom proof_of_OSTaskNameSet_safety_wit_7 : OSTaskNameSet_safety_wit_7.
Axiom proof_of_OSTaskNameSet_safety_wit_8 : OSTaskNameSet_safety_wit_8.
Axiom proof_of_OSTaskNameSet_safety_wit_9 : OSTaskNameSet_safety_wit_9.
Axiom proof_of_OSTaskNameSet_entail_wit_1_1 : OSTaskNameSet_entail_wit_1_1.
Axiom proof_of_OSTaskNameSet_entail_wit_1_2 : OSTaskNameSet_entail_wit_1_2.
Axiom proof_of_OSTaskNameSet_entail_wit_2 : OSTaskNameSet_entail_wit_2.
Axiom proof_of_OSTaskNameSet_entail_wit_3 : OSTaskNameSet_entail_wit_3.
Axiom proof_of_OSTaskNameSet_entail_wit_4_1 : OSTaskNameSet_entail_wit_4_1.
Axiom proof_of_OSTaskNameSet_entail_wit_4_2 : OSTaskNameSet_entail_wit_4_2.
Axiom proof_of_OSTaskNameSet_entail_wit_5 : OSTaskNameSet_entail_wit_5.
Axiom proof_of_OSTaskNameSet_entail_wit_6 : OSTaskNameSet_entail_wit_6.
Axiom proof_of_OSTaskNameSet_entail_wit_7 : OSTaskNameSet_entail_wit_7.
Axiom proof_of_OSTaskNameSet_entail_wit_8 : OSTaskNameSet_entail_wit_8.
Axiom proof_of_OSTaskNameSet_entail_wit_9 : OSTaskNameSet_entail_wit_9.
Axiom proof_of_OSTaskNameSet_return_wit_1 : OSTaskNameSet_return_wit_1.
Axiom proof_of_OSTaskNameSet_return_wit_2 : OSTaskNameSet_return_wit_2.
Axiom proof_of_OSTaskNameSet_return_wit_3 : OSTaskNameSet_return_wit_3.
Axiom proof_of_OSTaskNameSet_return_wit_4 : OSTaskNameSet_return_wit_4.
Axiom proof_of_OSTaskNameSet_return_wit_5 : OSTaskNameSet_return_wit_5.
Axiom proof_of_OSTaskNameSet_return_wit_6 : OSTaskNameSet_return_wit_6.
Axiom proof_of_OSTaskNameSet_return_wit_7 : OSTaskNameSet_return_wit_7.
Axiom proof_of_OSTaskNameSet_return_wit_8 : OSTaskNameSet_return_wit_8.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_1 : OSTaskNameSet_partial_solve_wit_1.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_2 : OSTaskNameSet_partial_solve_wit_2.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_3 : OSTaskNameSet_partial_solve_wit_3.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_4 : OSTaskNameSet_partial_solve_wit_4.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_5 : OSTaskNameSet_partial_solve_wit_5.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_6 : OSTaskNameSet_partial_solve_wit_6.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_7 : OSTaskNameSet_partial_solve_wit_7.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_8 : OSTaskNameSet_partial_solve_wit_8.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_9 : OSTaskNameSet_partial_solve_wit_9.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_10 : OSTaskNameSet_partial_solve_wit_10.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_11_pure : OSTaskNameSet_partial_solve_wit_11_pure.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_11 : OSTaskNameSet_partial_solve_wit_11.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_12_pure : OSTaskNameSet_partial_solve_wit_12_pure.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_12 : OSTaskNameSet_partial_solve_wit_12.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_13_pure : OSTaskNameSet_partial_solve_wit_13_pure.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_13 : OSTaskNameSet_partial_solve_wit_13.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_14_pure : OSTaskNameSet_partial_solve_wit_14_pure.
Axiom proof_of_OSTaskNameSet_partial_solve_wit_14 : OSTaskNameSet_partial_solve_wit_14.
Axiom proof_of_OSTaskNameSet_which_implies_wit_1 : OSTaskNameSet_which_implies_wit_1.
Axiom proof_of_OSTaskNameSet_which_implies_wit_2 : OSTaskNameSet_which_implies_wit_2.
Axiom proof_of_OSTaskNameSet_which_implies_wit_3 : OSTaskNameSet_which_implies_wit_3.
Axiom proof_of_OSTaskNameSet_which_implies_wit_4 : OSTaskNameSet_which_implies_wit_4.
Axiom proof_of_OSTaskNameSet_which_implies_wit_5 : OSTaskNameSet_which_implies_wit_5.

End VC_Correct.
