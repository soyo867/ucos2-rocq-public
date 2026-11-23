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
Require Import Ucos2Verify.VC.code.task.spec.task_reg_set_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskRegSet -----*)

Definition OSTaskRegSet_safety_wit_1 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (id_pre < 1)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre >= 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH8 : (0 <= value_pre)) (PreH9 : (value_pre < 4294967296)) (PreH10 : (0 <= id_pre)) (PreH11 : (id_pre < 256)) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre < 256)) (PreH14 : (value_pre <= UINT_MAX)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (value_pre >= 0)) (PreH17 : (0 >= 0)) (PreH18 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegSet_safety_wit_2 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (id_pre < 1)) (PreH4 : (prio_pre < 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH7 : (0 <= value_pre)) (PreH8 : (value_pre < 4294967296)) (PreH9 : (0 <= id_pre)) (PreH10 : (id_pre < 256)) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 256)) (PreH13 : (value_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (value_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_raw_rep sg entry )
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegSet_safety_wit_3 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= prio_pre)) (PreH2 : (task_reg_set_priority_valid prio_pre )) (PreH3 : (id_pre = 0)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < 4294967296)) (PreH6 : (ptcb = (task_reg_set_pointer (sg) (entry) (prio_pre)))) (PreH7 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegSet_safety_wit_4 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 0)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (ptcb = (task_reg_set_pointer (sg) (entry) (prio_pre)))) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (critical_region_interval critical sg invocation before entry )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskRegSet_safety_wit_5 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegSet_safety_wit_6 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (after_caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegSet_entail_wit_1 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 256) ” 
  &&  “ (value_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (value_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (value_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (value_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  TT && emp 
|--
  “ (prio_pre < 256) ” 
  &&  “ (0 <= prio_pre) ”
  &&  emp
).

Definition OSTaskRegSet_entail_wit_1_split_goal_1 := 
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (value_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (value_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (prio_pre < 256)
.

Definition OSTaskRegSet_entail_wit_1_split_goal_2 := 
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (value_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (value_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (0 <= prio_pre)
.

Definition OSTaskRegSet_entail_wit_2 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 256)) (PreH3 : (value_pre <= UINT_MAX)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (value_pre >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
|--
  “ (0 <= id_pre) ” 
  &&  “ (id_pre < 256) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 256) ” 
  &&  “ (value_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (value_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 256)) (PreH3 : (value_pre <= UINT_MAX)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (value_pre >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  TT && emp 
|--
  “ (id_pre < 256) ” 
  &&  “ (0 <= id_pre) ”
  &&  emp
).

Definition OSTaskRegSet_entail_wit_2_split_goal_1 := 
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 256)) (PreH3 : (value_pre <= UINT_MAX)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (value_pre >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (id_pre < 256)
.

Definition OSTaskRegSet_entail_wit_2_split_goal_2 := 
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 256)) (PreH3 : (value_pre <= UINT_MAX)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (value_pre >= 0)) (PreH6 : (0 >= 0)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (0 <= id_pre)
.

Definition OSTaskRegSet_entail_wit_3 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= id_pre)) (PreH2 : (id_pre < 256)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 256)) (PreH5 : (value_pre <= UINT_MAX)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (value_pre >= 0)) (PreH8 : (0 >= 0)) (PreH9 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
|--
  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (0 <= id_pre) ” 
  &&  “ (id_pre < 256) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 256) ” 
  &&  “ (value_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (value_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
.

Definition OSTaskRegSet_entail_wit_4_1 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (id_pre < 1)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre >= 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH8 : (0 <= value_pre)) (PreH9 : (value_pre < 4294967296)) (PreH10 : (0 <= id_pre)) (PreH11 : (id_pre < 256)) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre < 256)) (PreH14 : (value_pre <= UINT_MAX)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (value_pre >= 0)) (PreH17 : (0 >= 0)) (PreH18 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (id_pre < 1)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre >= 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH8 : (0 <= value_pre)) (PreH9 : (value_pre < 4294967296)) (PreH10 : (0 <= id_pre)) (PreH11 : (id_pre < 256)) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre < 256)) (PreH14 : (value_pre <= UINT_MAX)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (value_pre >= 0)) (PreH17 : (0 >= 0)) (PreH18 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
  **  (caller )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
).

Definition OSTaskRegSet_entail_wit_4_2 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (id_pre < 1)) (PreH4 : (prio_pre < 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH7 : (0 <= value_pre)) (PreH8 : (value_pre < 4294967296)) (PreH9 : (0 <= id_pre)) (PreH10 : (id_pre < 256)) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 256)) (PreH13 : (value_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (value_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (id_pre < 1)) (PreH4 : (prio_pre < 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH7 : (0 <= value_pre)) (PreH8 : (value_pre < 4294967296)) (PreH9 : (0 <= id_pre)) (PreH10 : (id_pre < 256)) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 256)) (PreH13 : (value_pre <= UINT_MAX)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (value_pre >= 0)) (PreH16 : (0 >= 0)) (PreH17 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_raw_rep sg entry_2 )
  **  (caller )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
).

Definition OSTaskRegSet_entail_wit_5 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) = 255)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_set_current_pointer (sg) (entry)))
  **  (task_reg_set_current_frame sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) = 255)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_set_current_pointer (sg) (entry)))
  **  (task_reg_set_current_frame sg entry )
  **  (caller )
).

Definition OSTaskRegSet_entail_wit_6 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) <> 255)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_set_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_set_table_frame sg entry prio_pre )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) <> 255)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_set_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_set_table_frame sg entry prio_pre )
  **  (caller )
).

Definition OSTaskRegSet_entail_wit_7_1 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre = 255)) (PreH2 : (id_pre = 0)) (PreH3 : (0 <= value_pre)) (PreH4 : (value_pre < 4294967296)) (PreH5 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_set_current_pointer (sg) (entry)))
  **  (task_reg_set_current_frame sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ ((task_reg_set_current_pointer (sg) (entry)) = (task_reg_set_pointer (sg) (entry_2) (prio_pre))) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre = 255)) (PreH2 : (id_pre = 0)) (PreH3 : (0 <= value_pre)) (PreH4 : (value_pre < 4294967296)) (PreH5 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (critical_region_interval critical sg invocation before entry )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_set_current_pointer (sg) (entry)))
  **  (task_reg_set_current_frame sg entry )
  **  (caller )
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ ((task_reg_set_current_pointer (sg) (entry)) = (task_reg_set_pointer (sg) (entry_2) (prio_pre))) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
).

Definition OSTaskRegSet_entail_wit_7_2 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 63)) (PreH3 : (id_pre = 0)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < 4294967296)) (PreH6 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_set_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_set_table_frame sg entry prio_pre )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ ((task_reg_set_table_pointer (sg) (entry) (prio_pre)) = (task_reg_set_pointer (sg) (entry_2) (prio_pre))) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 63)) (PreH3 : (id_pre = 0)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < 4294967296)) (PreH6 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_set_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_set_table_frame sg entry prio_pre )
  **  (caller )
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ ((task_reg_set_table_pointer (sg) (entry) (prio_pre)) = (task_reg_set_pointer (sg) (entry_2) (prio_pre))) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (UCOS2_state_inv sg entry_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
).

Definition OSTaskRegSet_entail_wit_8_1 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  TT && emp 
|--
  “ (task_reg_set_effect sg entry_2 caller prio_pre 0 value_pre 0 67 entry_2 caller ) ”
  &&  emp
).

Definition OSTaskRegSet_entail_wit_8_1_split_goal_1 := 
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 0)) (PreH2 : (0 <= prio_pre)) (PreH3 : (task_reg_set_priority_valid prio_pre )) (PreH4 : (id_pre = 0)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH8 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (critical_region_interval critical sg invocation before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_effect sg entry_2 caller prio_pre 0 value_pre 0 67 entry_2 caller )
.

Definition OSTaskRegSet_entail_wit_8_2 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (task_reg_set_priority_valid prio_pre )) (PreH5 : (id_pre = 0)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH9 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (critical_region_interval critical sg invocation before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (task_reg_set_priority_valid prio_pre )) (PreH5 : (id_pre = 0)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH9 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (critical_region_interval critical sg invocation before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  TT && emp 
|--
  “ (task_reg_set_effect sg entry_2 caller prio_pre 0 value_pre 1 67 entry_2 caller ) ”
  &&  emp
).

Definition OSTaskRegSet_entail_wit_8_2_split_goal_1 := 
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (task_reg_set_priority_valid prio_pre )) (PreH5 : (id_pre = 0)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH9 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (critical_region_interval critical sg invocation before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_effect sg entry_2 caller prio_pre 0 value_pre 1 67 entry_2 caller )
.

Definition OSTaskRegSet_entail_wit_9 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (task_reg_set_priority_valid prio_pre )) (PreH5 : (id_pre = 0)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH9 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (critical_region_interval critical sg invocation before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (released: UCOS2_Verify_State)  (after_caller: Assertion)  (residual: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (ptcb = (task_reg_set_pointer (sg) (entry) (prio_pre))) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_store_closure sg entry caller ptcb value_pre released after_caller residual ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (residual )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (ptcb: Z) (cpu_sr: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (task_reg_set_priority_valid prio_pre )) (PreH5 : (id_pre = 0)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH9 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (critical_region_interval critical sg invocation before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (released: UCOS2_Verify_State)  (after_caller: Assertion)  (residual: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (ptcb = (task_reg_set_pointer (sg) (entry) (prio_pre))) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_store_closure sg entry caller ptcb value_pre released after_caller residual ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (residual )
).

Definition OSTaskRegSet_entail_wit_10 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (released_2: UCOS2_Verify_State) (after_caller_2: Assertion) (residual: Assertion) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= prio_pre)) (PreH2 : (task_reg_set_priority_valid prio_pre )) (PreH3 : (id_pre = 0)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < 4294967296)) (PreH6 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (critical_region_interval critical sg invocation before entry_2 )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_reg_set_store_closure sg entry_2 caller ptcb value_pre released_2 after_caller_2 residual )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") (0 + 1 ) 1 )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |-> value_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (residual )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (released: UCOS2_Verify_State)  (after_caller: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (released_2: UCOS2_Verify_State) (after_caller_2: Assertion) (residual: Assertion) (ptcb: Z) (cpu_sr: Z) (PreH1 : (value_pre <= UINT_MAX)) (PreH2 : (value_pre >= 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (task_reg_set_priority_valid prio_pre )) (PreH5 : (id_pre = 0)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (ptcb = (task_reg_set_pointer (sg) (entry_2) (prio_pre)))) (PreH9 : (ptcb <> 0)) (PreH10 : (ptcb <> 1)) (PreH11 : (critical_region_interval critical sg invocation before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (task_reg_set_store_closure sg entry_2 caller ptcb value_pre released_2 after_caller_2 residual )) (PreH14 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |-> value_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (residual )
|--
  EX (released: UCOS2_Verify_State)  (after_caller: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg released )
  **  (after_caller )
).

Definition OSTaskRegSet_return_wit_1 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
) \/
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
).

Definition OSTaskRegSet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
.

Definition OSTaskRegSet_return_wit_2 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (0 <= id_pre)) (PreH9 : (id_pre < 256)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 256)) (PreH12 : (value_pre <= UINT_MAX)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (value_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
) \/
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (0 <= id_pre)) (PreH9 : (id_pre < 256)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 256)) (PreH12 : (value_pre <= UINT_MAX)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (value_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
).

Definition OSTaskRegSet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (0 <= id_pre)) (PreH9 : (id_pre < 256)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 256)) (PreH12 : (value_pre <= UINT_MAX)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (value_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
.

Definition OSTaskRegSet_return_wit_3 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
) \/
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
).

Definition OSTaskRegSet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
.

Definition OSTaskRegSet_return_wit_4 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 42)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
) \/
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 42)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
).

Definition OSTaskRegSet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 42)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
.

Definition OSTaskRegSet_return_wit_5 := 
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
) \/
(
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
).

Definition OSTaskRegSet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_restore_post platform critical sg invocation origin cpu_sr released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (task_reg_set_post platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller X )
.

Definition OSTaskRegSet_partial_solve_wit_1 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < 4294967296)) (PreH3 : (0 <= id_pre)) (PreH4 : (id_pre < 256)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre < 256)) (PreH7 : (value_pre <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (value_pre >= 0)) (PreH10 : (0 >= 0)) (PreH11 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
|--
  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (0 <= id_pre) ” 
  &&  “ (id_pre < 256) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 256) ” 
  &&  “ (value_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (value_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (task_reg_set_pre platform critical sg invocation origin mask before prio_pre id_pre value_pre perr_pre caller )
.

Definition OSTaskRegSet_partial_solve_wit_2 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre < 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < 4294967296)) (PreH8 : (0 <= id_pre)) (PreH9 : (id_pre < 256)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 256)) (PreH12 : (value_pre <= UINT_MAX)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (value_pre >= 0)) (PreH15 : (0 >= 0)) (PreH16 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (id_pre < 1) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre >= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (0 <= id_pre) ” 
  &&  “ (id_pre < 256) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 256) ” 
  &&  “ (value_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (value_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegSet_partial_solve_wit_3 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre < 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller )) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < 4294967296)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre < 256)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 256)) (PreH11 : (value_pre <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (value_pre >= 0)) (PreH14 : (0 >= 0)) (PreH15 : (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (id_pre < 1) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio_pre id_pre value_pre caller ) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (0 <= id_pre) ” 
  &&  “ (id_pre < 256) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 256) ” 
  &&  “ (value_pre <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (value_pre >= 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (task_reg_set_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegSet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskRegSet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 67 entry caller ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegSet_partial_solve_wit_4 := OSTaskRegSet_partial_solve_wit_4_pure -> OSTaskRegSet_partial_solve_wit_4_aux.

Definition OSTaskRegSet_partial_solve_wit_5 := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (residual: Assertion) (ptcb: Z) (cpu_sr: Z) (PreH1 : (0 <= prio_pre)) (PreH2 : (task_reg_set_priority_valid prio_pre )) (PreH3 : (id_pre = 0)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < 4294967296)) (PreH6 : (ptcb = (task_reg_set_pointer (sg) (entry) (prio_pre)))) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (critical_region_interval critical sg invocation before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_reg_set_store_closure sg entry caller ptcb value_pre released after_caller residual )) (PreH12 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (residual )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (task_reg_set_priority_valid prio_pre ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < 4294967296) ” 
  &&  “ (ptcb = (task_reg_set_pointer (sg) (entry) (prio_pre))) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_store_closure sg entry caller ptcb value_pre released after_caller residual ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") id_pre 0 1 )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (residual )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegSet_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "value" ) )) # UInt  |-> value_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskRegSet_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (value_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (released: UCOS2_Verify_State) (after_caller: Assertion) (cpu_sr: Z) (ptcb: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller )) (PreH4 : (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_reg_set_effect sg entry caller prio_pre id_pre value_pre ptcb 0 released after_caller ) ” 
  &&  “ (task_reg_set_safe critical sg invocation before caller prio_pre id_pre value_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg released )
  **  (after_caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegSet_partial_solve_wit_6 := OSTaskRegSet_partial_solve_wit_6_pure -> OSTaskRegSet_partial_solve_wit_6_aux.

Definition OSTaskRegSet_which_implies_wit_1 := 
(
forall (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) (value: Z) (id: Z) (prio: Z) ,
  (task_reg_set_pre platform critical sg invocation origin mask before prio id value perr caller )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio id value caller ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr) # UChar  |->_)
) \/
(
forall (caller: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) (value: Z) (id: Z) (prio: Z) ,
  (task_reg_set_pre platform critical sg invocation origin mask before prio id value perr caller )
|--
  EX (x: Z) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_set_self_admission critical sg invocation before prio id value caller ) ”
  &&  ((perr) # UChar  |-> x)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
).

Module Type VC_Correct.


Axiom proof_of_OSTaskRegSet_safety_wit_1 : OSTaskRegSet_safety_wit_1.
Axiom proof_of_OSTaskRegSet_safety_wit_2 : OSTaskRegSet_safety_wit_2.
Axiom proof_of_OSTaskRegSet_safety_wit_3 : OSTaskRegSet_safety_wit_3.
Axiom proof_of_OSTaskRegSet_safety_wit_4 : OSTaskRegSet_safety_wit_4.
Axiom proof_of_OSTaskRegSet_safety_wit_5 : OSTaskRegSet_safety_wit_5.
Axiom proof_of_OSTaskRegSet_safety_wit_6 : OSTaskRegSet_safety_wit_6.
Axiom proof_of_OSTaskRegSet_entail_wit_1 : OSTaskRegSet_entail_wit_1.
Axiom proof_of_OSTaskRegSet_entail_wit_2 : OSTaskRegSet_entail_wit_2.
Axiom proof_of_OSTaskRegSet_entail_wit_3 : OSTaskRegSet_entail_wit_3.
Axiom proof_of_OSTaskRegSet_entail_wit_4_1 : OSTaskRegSet_entail_wit_4_1.
Axiom proof_of_OSTaskRegSet_entail_wit_4_2 : OSTaskRegSet_entail_wit_4_2.
Axiom proof_of_OSTaskRegSet_entail_wit_5 : OSTaskRegSet_entail_wit_5.
Axiom proof_of_OSTaskRegSet_entail_wit_6 : OSTaskRegSet_entail_wit_6.
Axiom proof_of_OSTaskRegSet_entail_wit_7_1 : OSTaskRegSet_entail_wit_7_1.
Axiom proof_of_OSTaskRegSet_entail_wit_7_2 : OSTaskRegSet_entail_wit_7_2.
Axiom proof_of_OSTaskRegSet_entail_wit_8_1 : OSTaskRegSet_entail_wit_8_1.
Axiom proof_of_OSTaskRegSet_entail_wit_8_2 : OSTaskRegSet_entail_wit_8_2.
Axiom proof_of_OSTaskRegSet_entail_wit_9 : OSTaskRegSet_entail_wit_9.
Axiom proof_of_OSTaskRegSet_entail_wit_10 : OSTaskRegSet_entail_wit_10.
Axiom proof_of_OSTaskRegSet_return_wit_1 : OSTaskRegSet_return_wit_1.
Axiom proof_of_OSTaskRegSet_return_wit_2 : OSTaskRegSet_return_wit_2.
Axiom proof_of_OSTaskRegSet_return_wit_3 : OSTaskRegSet_return_wit_3.
Axiom proof_of_OSTaskRegSet_return_wit_4 : OSTaskRegSet_return_wit_4.
Axiom proof_of_OSTaskRegSet_return_wit_5 : OSTaskRegSet_return_wit_5.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_1 : OSTaskRegSet_partial_solve_wit_1.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_2 : OSTaskRegSet_partial_solve_wit_2.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_3 : OSTaskRegSet_partial_solve_wit_3.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_4_pure : OSTaskRegSet_partial_solve_wit_4_pure.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_4 : OSTaskRegSet_partial_solve_wit_4.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_5 : OSTaskRegSet_partial_solve_wit_5.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_6_pure : OSTaskRegSet_partial_solve_wit_6_pure.
Axiom proof_of_OSTaskRegSet_partial_solve_wit_6 : OSTaskRegSet_partial_solve_wit_6.
Axiom proof_of_OSTaskRegSet_which_implies_wit_1 : OSTaskRegSet_which_implies_wit_1.

End VC_Correct.
