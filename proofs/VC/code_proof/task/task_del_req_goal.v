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
Require Import Ucos2Verify.VC.code.task.spec.task_del_req_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskDelReq -----*)

Definition OSTaskDelReq_safety_wit_1 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = request)) (PreH2 : (0 <= request)) (PreH3 : (request <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition OSTaskDelReq_safety_wit_2 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (prio_pre <> 63)) (PreH5 : (prio_pre = request)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSTaskDelReq_safety_wit_3 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre < 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (0 <= request)) (PreH6 : (request <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSTaskDelReq_safety_wit_4 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre >= 63)) (PreH6 : (prio_pre <> 63)) (PreH7 : (prio_pre = request)) (PreH8 : (0 <= request)) (PreH9 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_safety_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (stat: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current )) (PreH2 : (request = 255)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current )
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  ((( &( "stat" ) )) # UChar  |-> stat)
  **  (coq_prop (task_del_req_step (request) (acquired) (stat) (acquired)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_safety_wit_6 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (prio_pre <> 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 63)) (PreH6 : (prio_pre = request)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_safety_wit_7 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) (PreH3 : (ptcb = (task_del_req_table_entry (sg) (acquired) (request)))) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_safety_wit_8 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current )
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_safety_wit_9 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 0)) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) (PreH4 : (ptcb = (task_del_req_table_entry (sg) (acquired) (request)))) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskDelReq_safety_wit_10 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current )
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_safety_wit_11 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation released current )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current )
  **  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskDelReq_entail_wit_1 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre >= 63)) (PreH6 : (prio_pre <> 63)) (PreH7 : (prio_pre = request)) (PreH8 : (0 <= request)) (PreH9 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  EX (tid: Z)  (task: TaskAbstractState)  (acquired: UCOS2_Verify_State) ,
  “ (request = 255) ”
  &&  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (coq_prop (task_del_req_current (acquired) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> (encode_task_delete_request ((delReq (task)))))
  **  (task_del_req_self_frame sg acquired tid task )
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre >= 63)) (PreH6 : (prio_pre <> 63)) (PreH7 : (prio_pre = request)) (PreH8 : (0 <= request)) (PreH9 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  EX (tid: Z)  (task: TaskAbstractState)  (acquired: UCOS2_Verify_State) ,
  “ (prio_pre = request) ” 
  &&  “ (request = 255) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (coq_prop (task_del_req_current (acquired) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> (encode_task_delete_request ((delReq (task)))))
  **  (task_del_req_self_frame sg acquired tid task )
).

Definition OSTaskDelReq_entail_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (tid: Z) (task: TaskAbstractState) (cpu_sr: Z) (PreH1 : (request = 255)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (coq_prop (task_del_req_current (acquired_2) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> (encode_task_delete_request ((delReq (task)))))
  **  (task_del_req_self_frame sg acquired_2 tid task )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (request = 255) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) ((encode_task_delete_request ((delReq (task))))) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (tid: Z) (task: TaskAbstractState) (cpu_sr: Z) (PreH1 : (request = 255)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (coq_prop (task_del_req_current (acquired_2) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> (encode_task_delete_request ((delReq (task)))))
  **  (task_del_req_self_frame sg acquired_2 tid task )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (request = 255) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) ((encode_task_delete_request ((delReq (task))))) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskDelReq_entail_wit_3 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (prio_pre <> 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 63)) (PreH6 : (prio_pre = request)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (((( &( "OSTCBPrioTbl" ) ) + (request * sizeof(PTR)))) # Ptr  |-> (task_del_req_table_entry (sg) (acquired) (request)))
  **  (task_del_req_table_frame sg acquired request )
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (prio_pre <> 255)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 63)) (PreH6 : (prio_pre = request)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (prio_pre = request) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (((( &( "OSTCBPrioTbl" ) ) + (request * sizeof(PTR)))) # Ptr  |-> (task_del_req_table_entry (sg) (acquired) (request)))
  **  (task_del_req_table_frame sg acquired request )
).

Definition OSTaskDelReq_entail_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (((( &( "OSTCBPrioTbl" ) ) + (request * sizeof(PTR)))) # Ptr  |-> (task_del_req_table_entry (sg) (acquired) (request)))
  **  (task_del_req_table_frame sg acquired request )
|--
  EX (acquired_2: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ” 
  &&  “ ((task_del_req_table_entry (sg) (acquired) (request)) = (task_del_req_table_entry (sg) (acquired_2) (request))) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (((( &( "OSTCBPrioTbl" ) ) + (request * sizeof(PTR)))) # Ptr  |-> (task_del_req_table_entry (sg) (acquired) (request)))
  **  (task_del_req_table_frame sg acquired request )
|--
  EX (acquired_2: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ” 
  &&  “ ((task_del_req_table_entry (sg) (acquired) (request)) = (task_del_req_table_entry (sg) (acquired_2) (request))) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
).

Definition OSTaskDelReq_entail_wit_5 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) (PreH4 : (ptcb = (task_del_req_table_entry (sg) (acquired_2) (request)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) (PreH4 : (ptcb = (task_del_req_table_entry (sg) (acquired_2) (request)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskDelReq_entail_wit_6 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= request)) (PreH4 : (request < 63)) (PreH5 : (ptcb = (task_del_req_table_entry (sg) (acquired_2) (request)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= request)) (PreH4 : (request < 63)) (PreH5 : (ptcb = (task_del_req_table_entry (sg) (acquired_2) (request)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
).

Definition OSTaskDelReq_entail_wit_7 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= request)) (PreH4 : (request < 63)) (PreH5 : (ptcb = (task_del_req_table_entry (sg) (acquired_2) (request)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (task: TaskAbstractState)  (acquired: UCOS2_Verify_State)  (tid: Z) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (coq_prop (task_del_req_target (acquired) (request) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> (encode_task_delete_request ((delReq (task)))))
  **  (task_del_req_field_frame sg acquired tid task )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= request)) (PreH4 : (request < 63)) (PreH5 : (ptcb = (task_del_req_table_entry (sg) (acquired_2) (request)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  (UCOS2_inv sg acquired_2 )
|--
  EX (task: TaskAbstractState)  (acquired: UCOS2_Verify_State)  (tid: Z) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ” 
  &&  “ (ptcb = (task_slot_addr (sg) (tid))) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired)) )
  **  (coq_prop (task_del_req_target (acquired) (request) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> (encode_task_delete_request ((delReq (task)))))
  **  (task_del_req_field_frame sg acquired tid task )
).

Definition OSTaskDelReq_entail_wit_8 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (tid: Z) (task: TaskAbstractState) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) (PreH3 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (coq_prop (task_del_req_target (acquired_2) (request) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 63)
  **  (task_del_req_field_frame sg acquired_2 tid task )
|--
  EX (released: UCOS2_Verify_State)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (tid: Z) (task: TaskAbstractState) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) (PreH3 : (ptcb = (task_slot_addr (sg) (tid)))) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired_2)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (UCOS2_state_inv (sg) (acquired_2)) )
  **  (coq_prop (task_del_req_target (acquired_2) (request) (tid) (task)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 63)
  **  (task_del_req_field_frame sg acquired_2 tid task )
|--
  EX (released: UCOS2_Verify_State)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
).

Definition OSTaskDelReq_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (cpu_sr: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation released current_2 )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (0) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (cpu_sr: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation released current_2 )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (0) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
).

Definition OSTaskDelReq_return_wit_2 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current_2 )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (61) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current_2 )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (61) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
).

Definition OSTaskDelReq_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current_2 )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (67) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current_2 )) (PreH2 : (0 <= request)) (PreH3 : (request < 63)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (67) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
).

Definition OSTaskDelReq_return_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (stat: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current_2 )) (PreH2 : (request = 255)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (stat) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (stat) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (stat: Z) (current_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation acquired current_2 )) (PreH2 : (request = 255)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation current_2 )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (stat) (acquired)) )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (stat) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
).

Definition OSTaskDelReq_return_wit_5 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (0 <= request)) (PreH6 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (42) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (0 <= request)) (PreH6 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (42) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
).

Definition OSTaskDelReq_return_wit_6 := 
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 63)) (PreH2 : (prio_pre = request)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (62) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
) \/
(
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 63)) (PreH2 : (prio_pre = request)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  EX (current: UCOS2_Verify_State) ,
  (coq_prop (task_del_req_post (critical) (sg) (invocation) (request) (before) (62) (current) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask current )
).

Definition OSTaskDelReq_partial_solve_wit_1 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (prio_pre <> 63)) (PreH5 : (prio_pre = request)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre >= 63) ” 
  &&  “ (prio_pre <> 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (task_del_req_closed platform critical sg invocation origin mask before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
.

Definition OSTaskDelReq_partial_solve_wit_2 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (prio_pre <> 63)) (PreH5 : (prio_pre = request)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre >= 63) ” 
  &&  “ (prio_pre <> 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
.

Definition OSTaskDelReq_partial_solve_wit_3_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (stat: Z) (PreH1 : (request = 255)) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  ((( &( "stat" ) )) # UChar  |-> stat)
  **  (coq_prop (task_del_req_step (request) (acquired) (stat) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskDelReq_partial_solve_wit_3_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (stat: Z) (PreH1 : (request = 255)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (stat) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (request = 255) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (stat) (acquired)) )
.

Definition OSTaskDelReq_partial_solve_wit_3 := OSTaskDelReq_partial_solve_wit_3_pure -> OSTaskDelReq_partial_solve_wit_3_aux.

Definition OSTaskDelReq_partial_solve_wit_4 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre < 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (0 <= request)) (PreH6 : (request <= 255)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (task_del_req_closed platform critical sg invocation origin mask before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
.

Definition OSTaskDelReq_partial_solve_wit_5 := 
forall (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre < 63)) (PreH3 : (prio_pre <> 63)) (PreH4 : (prio_pre = request)) (PreH5 : (0 <= request)) (PreH6 : (request <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
|--
  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 63) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (task_del_req_addresses (sg) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_del_req_admission (critical) (sg) (invocation) (request) (before)) )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
.

Definition OSTaskDelReq_partial_solve_wit_6_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskDelReq_partial_solve_wit_6_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (67) (acquired)) )
.

Definition OSTaskDelReq_partial_solve_wit_6 := OSTaskDelReq_partial_solve_wit_6_pure -> OSTaskDelReq_partial_solve_wit_6_aux.

Definition OSTaskDelReq_partial_solve_wit_7_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskDelReq_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (61) (acquired)) )
.

Definition OSTaskDelReq_partial_solve_wit_7 := OSTaskDelReq_partial_solve_wit_7_pure -> OSTaskDelReq_partial_solve_wit_7_aux.

Definition OSTaskDelReq_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "stat" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskDelReq_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= request)) (PreH2 : (request < 63)) ,
  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 63) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg released )
  **  (coq_prop (task_del_req_safe (critical) (sg) (invocation) (request) (before) (X)) )
  **  (coq_prop (critical_region_interval (critical) (sg) (invocation) (before) (acquired)) )
  **  (coq_prop (interrupt_saved_value (mask) (cpu_sr)) )
  **  (coq_prop (task_del_req_step (request) (acquired) (0) (released)) )
.

Definition OSTaskDelReq_partial_solve_wit_8 := OSTaskDelReq_partial_solve_wit_8_pure -> OSTaskDelReq_partial_solve_wit_8_aux.

Definition OSTaskDelReq_which_implies_wit_1 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSTaskDelReq_which_implies_wit_1_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSTaskDelReq_which_implies_wit_2 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSTaskDelReq_which_implies_wit_2_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_del_req_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
.

Module Type VC_Correct.


Axiom proof_of_OSTaskDelReq_safety_wit_1 : OSTaskDelReq_safety_wit_1.
Axiom proof_of_OSTaskDelReq_safety_wit_2 : OSTaskDelReq_safety_wit_2.
Axiom proof_of_OSTaskDelReq_safety_wit_3 : OSTaskDelReq_safety_wit_3.
Axiom proof_of_OSTaskDelReq_safety_wit_4 : OSTaskDelReq_safety_wit_4.
Axiom proof_of_OSTaskDelReq_safety_wit_5 : OSTaskDelReq_safety_wit_5.
Axiom proof_of_OSTaskDelReq_safety_wit_6 : OSTaskDelReq_safety_wit_6.
Axiom proof_of_OSTaskDelReq_safety_wit_7 : OSTaskDelReq_safety_wit_7.
Axiom proof_of_OSTaskDelReq_safety_wit_8 : OSTaskDelReq_safety_wit_8.
Axiom proof_of_OSTaskDelReq_safety_wit_9 : OSTaskDelReq_safety_wit_9.
Axiom proof_of_OSTaskDelReq_safety_wit_10 : OSTaskDelReq_safety_wit_10.
Axiom proof_of_OSTaskDelReq_safety_wit_11 : OSTaskDelReq_safety_wit_11.
Axiom proof_of_OSTaskDelReq_entail_wit_1 : OSTaskDelReq_entail_wit_1.
Axiom proof_of_OSTaskDelReq_entail_wit_2 : OSTaskDelReq_entail_wit_2.
Axiom proof_of_OSTaskDelReq_entail_wit_3 : OSTaskDelReq_entail_wit_3.
Axiom proof_of_OSTaskDelReq_entail_wit_4 : OSTaskDelReq_entail_wit_4.
Axiom proof_of_OSTaskDelReq_entail_wit_5 : OSTaskDelReq_entail_wit_5.
Axiom proof_of_OSTaskDelReq_entail_wit_6 : OSTaskDelReq_entail_wit_6.
Axiom proof_of_OSTaskDelReq_entail_wit_7 : OSTaskDelReq_entail_wit_7.
Axiom proof_of_OSTaskDelReq_entail_wit_8 : OSTaskDelReq_entail_wit_8.
Axiom proof_of_OSTaskDelReq_return_wit_1 : OSTaskDelReq_return_wit_1.
Axiom proof_of_OSTaskDelReq_return_wit_2 : OSTaskDelReq_return_wit_2.
Axiom proof_of_OSTaskDelReq_return_wit_3 : OSTaskDelReq_return_wit_3.
Axiom proof_of_OSTaskDelReq_return_wit_4 : OSTaskDelReq_return_wit_4.
Axiom proof_of_OSTaskDelReq_return_wit_5 : OSTaskDelReq_return_wit_5.
Axiom proof_of_OSTaskDelReq_return_wit_6 : OSTaskDelReq_return_wit_6.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_1 : OSTaskDelReq_partial_solve_wit_1.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_2 : OSTaskDelReq_partial_solve_wit_2.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_3_pure : OSTaskDelReq_partial_solve_wit_3_pure.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_3 : OSTaskDelReq_partial_solve_wit_3.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_4 : OSTaskDelReq_partial_solve_wit_4.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_5 : OSTaskDelReq_partial_solve_wit_5.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_6_pure : OSTaskDelReq_partial_solve_wit_6_pure.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_6 : OSTaskDelReq_partial_solve_wit_6.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_7_pure : OSTaskDelReq_partial_solve_wit_7_pure.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_7 : OSTaskDelReq_partial_solve_wit_7.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_8_pure : OSTaskDelReq_partial_solve_wit_8_pure.
Axiom proof_of_OSTaskDelReq_partial_solve_wit_8 : OSTaskDelReq_partial_solve_wit_8.
Axiom proof_of_OSTaskDelReq_which_implies_wit_1 : OSTaskDelReq_which_implies_wit_1.
Axiom proof_of_OSTaskDelReq_which_implies_wit_2 : OSTaskDelReq_which_implies_wit_2.

End VC_Correct.
