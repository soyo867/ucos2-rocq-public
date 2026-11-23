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
Require Import Ucos2Verify.VC.code.task.spec.task_reg_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskRegGet -----*)

Definition OSTaskRegGet_safety_wit_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre >= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre < 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_3 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = 255)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition OSTaskRegGet_safety_wit_4 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre = 255)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre < 63)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition OSTaskRegGet_safety_wit_5 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (prio_pre < 63)) (PreH7 : (id_pre = 0)) (PreH8 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH9 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_6 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (prio_pre = 255)) (PreH7 : (id_pre = 0)) (PreH8 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH9 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_7 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb <> 0)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = 255)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskRegGet_safety_wit_8 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb <> 0)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre < 63)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskRegGet_safety_wit_9 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre = 255)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_10 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre < 63)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_11 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre < 63)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_12 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_13 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_2: UCOS2_Verify_State) (residual_2: Assertion) (entry_3: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry_3 after )) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH4 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) (PreH7 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual_2 )) (PreH8 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH9 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH10 : (id_pre = 0)) (PreH11 : (ptcb <> 0)) (PreH12 : (ptcb <> 1)) (PreH13 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual )) (PreH14 : (ptcb <> 1)) (PreH15 : (ptcb <> 0)) (PreH16 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH19 : (0 <= prio_pre)) (PreH20 : (prio_pre <= 255)) (PreH21 : (prio_pre < 63)) (PreH22 : (id_pre = 0)) (PreH23 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH24 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH25 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_safety_wit_14 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_2: UCOS2_Verify_State) (residual_2: Assertion) (entry_3: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry_3 after )) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH4 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) (PreH7 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual_2 )) (PreH8 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH9 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH10 : (id_pre = 0)) (PreH11 : (ptcb <> 0)) (PreH12 : (ptcb <> 1)) (PreH13 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual )) (PreH14 : (ptcb <> 1)) (PreH15 : (ptcb <> 0)) (PreH16 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH19 : (0 <= prio_pre)) (PreH20 : (prio_pre <= 255)) (PreH21 : (prio_pre = 255)) (PreH22 : (id_pre = 0)) (PreH23 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH24 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH25 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskRegGet_entail_wit_1_1 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre >= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre >= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  TT && emp 
|--
  “ (task_reg_get_scalar_valid 255 id_pre ) ”
  &&  emp
).

Definition OSTaskRegGet_entail_wit_1_1_split_goal_1 := 
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre >= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (0 <= id_pre)) (PreH8 : (id_pre <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (task_reg_get_scalar_valid 255 id_pre )
.

Definition OSTaskRegGet_entail_wit_1_2 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre < 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre < 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  TT && emp 
|--
  “ (task_reg_get_scalar_valid prio_pre id_pre ) ”
  &&  emp
).

Definition OSTaskRegGet_entail_wit_1_2_split_goal_1 := 
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (id_pre < 1)) (PreH3 : (prio_pre < 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (task_reg_get_scalar_valid prio_pre id_pre )
.

Definition OSTaskRegGet_entail_wit_2_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_3: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_4 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_reg_get_selection sg entry_4 255 (task_reg_get_current_pointer (sg) (entry)) )) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (prio_pre = 255)) (PreH7 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre <= 255)) (PreH12 : (prio_pre = 255)) (PreH13 : (id_pre = 0)) (PreH14 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH15 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> 255)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_4 )
  **  (UCOS2_inv sg entry_4 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry_2 prio_pre (task_reg_get_current_pointer (sg) (entry)) ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_entail_wit_2_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_3: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (entry_4: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_4 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_reg_get_selection sg entry_4 prio_pre (task_reg_get_table_pointer (sg) (entry) (prio_pre)) )) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre <= 255)) (PreH14 : (prio_pre < 63)) (PreH15 : (id_pre = 0)) (PreH16 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH17 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_4 )
  **  (UCOS2_inv sg entry_4 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (entry_2: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry_2 prio_pre (task_reg_get_table_pointer (sg) (entry) (prio_pre)) ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_return_wit_1 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_2: UCOS2_Verify_State) (residual_2: Assertion) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry_3 after_2 )) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH4 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) (PreH7 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual_2 )) (PreH8 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH9 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH10 : (id_pre = 0)) (PreH11 : (ptcb <> 0)) (PreH12 : (ptcb <> 1)) (PreH13 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual )) (PreH14 : (ptcb <> 1)) (PreH15 : (ptcb <> 0)) (PreH16 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH19 : (0 <= prio_pre)) (PreH20 : (prio_pre <= 255)) (PreH21 : (prio_pre < 63)) (PreH22 : (id_pre = 0)) (PreH23 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH24 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH25 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error observed after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_2: UCOS2_Verify_State) (residual_2: Assertion) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry_3 after_2 )) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH4 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) (PreH7 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual_2 )) (PreH8 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH9 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH10 : (id_pre = 0)) (PreH11 : (ptcb <> 0)) (PreH12 : (ptcb <> 1)) (PreH13 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual )) (PreH14 : (ptcb <> 1)) (PreH15 : (ptcb <> 0)) (PreH16 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH19 : (0 <= prio_pre)) (PreH20 : (prio_pre <= 255)) (PreH21 : (prio_pre < 63)) (PreH22 : (id_pre = 0)) (PreH23 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH24 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH25 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 0 observed after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
).

Definition OSTaskRegGet_return_wit_2 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_2: UCOS2_Verify_State) (residual_2: Assertion) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry_3 after_2 )) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH4 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) (PreH7 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual_2 )) (PreH8 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH9 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH10 : (id_pre = 0)) (PreH11 : (ptcb <> 0)) (PreH12 : (ptcb <> 1)) (PreH13 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual )) (PreH14 : (ptcb <> 1)) (PreH15 : (ptcb <> 0)) (PreH16 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH19 : (0 <= prio_pre)) (PreH20 : (prio_pre <= 255)) (PreH21 : (prio_pre = 255)) (PreH22 : (id_pre = 0)) (PreH23 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH24 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH25 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error observed after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_2: UCOS2_Verify_State) (residual_2: Assertion) (entry_3: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry_3 after_2 )) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH4 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) (PreH7 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual_2 )) (PreH8 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH9 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH10 : (id_pre = 0)) (PreH11 : (ptcb <> 0)) (PreH12 : (ptcb <> 1)) (PreH13 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual )) (PreH14 : (ptcb <> 1)) (PreH15 : (ptcb <> 0)) (PreH16 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH19 : (0 <= prio_pre)) (PreH20 : (prio_pre <= 255)) (PreH21 : (prio_pre = 255)) (PreH22 : (id_pre = 0)) (PreH23 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH24 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH25 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 0 observed after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
).

Definition OSTaskRegGet_return_wit_3 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre = 255)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre = 255)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 67 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
).

Definition OSTaskRegGet_return_wit_4 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre < 63)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre < 63)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 67 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
).

Definition OSTaskRegGet_return_wit_5 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre < 63)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre < 63)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 67 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
).

Definition OSTaskRegGet_return_wit_6 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 67)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 67 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
).

Definition OSTaskRegGet_return_wit_7 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  TT && emp 
|--
  “ (task_reg_get_post critical sg invocation mask before caller 255 id_pre 8 0 before X ) ”
  &&  emp
).

Definition OSTaskRegGet_return_wit_7_split_goal_1 := 
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (task_reg_get_post critical sg invocation mask before caller 255 id_pre 8 0 before X )
.

Definition OSTaskRegGet_return_wit_8 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 8)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  TT && emp 
|--
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 8 0 before X ) ”
  &&  emp
).

Definition OSTaskRegGet_return_wit_8_split_goal_1 := 
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (id_pre >= 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 8 0 before X )
.

Definition OSTaskRegGet_return_wit_9 := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |-> 42)
|--
  EX (error: Z)  (after: UCOS2_Verify_State) ,
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre error 0 after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  ((perr_pre) # UChar  |-> error)
) \/
(
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  TT && emp 
|--
  “ (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 42 0 before X ) ”
  &&  emp
).

Definition OSTaskRegGet_return_wit_9_split_goal_1 := 
forall (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre >= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (task_reg_get_post critical sg invocation mask before caller prio_pre id_pre 42 0 before X )
.

Definition OSTaskRegGet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre < 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTaskRegGet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre < 1)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre >= 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (0 <= id_pre)) (PreH7 : (id_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (id_pre < 1) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre >= 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (0 <= id_pre) ” 
  &&  “ (id_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_1 := OSTaskRegGet_partial_solve_wit_1_pure -> OSTaskRegGet_partial_solve_wit_1_aux.

Definition OSTaskRegGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre < 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTaskRegGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (id_pre < 1)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (0 <= id_pre)) (PreH6 : (id_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (id_pre < 1) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (0 <= id_pre) ” 
  &&  “ (id_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_2 := OSTaskRegGet_partial_solve_wit_2_pure -> OSTaskRegGet_partial_solve_wit_2_aux.

Definition OSTaskRegGet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre = 255)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = 255)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (255 = 255) ”
.

Definition OSTaskRegGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre = 255)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = 255)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (255 = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> 255)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_3 := OSTaskRegGet_partial_solve_wit_3_pure -> OSTaskRegGet_partial_solve_wit_3_aux.

Definition OSTaskRegGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (255 = 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> 255)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  (task_reg_get_current_frame sg entry )
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (255 = 255) ” 
  &&  “ ((task_reg_get_current_pointer (sg) (entry)) = (task_reg_get_current_pointer (sg) (entry))) ”
.

Definition OSTaskRegGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (255 = 255)) (PreH4 : (prio_pre = 255)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  (task_reg_get_current_frame sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (255 = 255) ” 
  &&  “ ((task_reg_get_current_pointer (sg) (entry)) = (task_reg_get_current_pointer (sg) (entry))) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  (task_reg_get_current_frame sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_4 := OSTaskRegGet_partial_solve_wit_4_pure -> OSTaskRegGet_partial_solve_wit_4_aux.

Definition OSTaskRegGet_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre < 63)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ”
.

Definition OSTaskRegGet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre < 63)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_5 := OSTaskRegGet_partial_solve_wit_5_pure -> OSTaskRegGet_partial_solve_wit_5_aux.

Definition OSTaskRegGet_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH7 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre <= 255)) (PreH11 : (prio_pre < 63)) (PreH12 : (id_pre = 0)) (PreH13 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_get_table_frame sg entry prio_pre )
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry) (prio_pre)))
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ ((task_reg_get_table_pointer (sg) (entry) (prio_pre)) = (task_reg_get_table_pointer (sg) (entry) (prio_pre))) ”
.

Definition OSTaskRegGet_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH7 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre <= 255)) (PreH11 : (prio_pre < 63)) (PreH12 : (id_pre = 0)) (PreH13 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_get_table_frame sg entry prio_pre )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ ((task_reg_get_table_pointer (sg) (entry) (prio_pre)) = (task_reg_get_table_pointer (sg) (entry) (prio_pre))) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry) (prio_pre)))
  **  (task_reg_get_table_frame sg entry prio_pre )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_6 := OSTaskRegGet_partial_solve_wit_6_pure -> OSTaskRegGet_partial_solve_wit_6_aux.

Definition OSTaskRegGet_partial_solve_wit_7_pure := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 0)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = 255)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre = 255)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskRegGet_partial_solve_wit_7_pure_split_goal_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre = 255)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskRegGet_partial_solve_wit_7_pure_split_goal_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre = 255)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskRegGet_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 0)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = 255)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (ptcb = 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_7 := OSTaskRegGet_partial_solve_wit_7_pure -> OSTaskRegGet_partial_solve_wit_7_aux.

Definition OSTaskRegGet_partial_solve_wit_8_pure := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 0)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre < 63)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre < 63)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskRegGet_partial_solve_wit_8_pure_split_goal_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre < 63)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskRegGet_partial_solve_wit_8_pure_split_goal_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 0)) (PreH4 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (prio_pre < 63)) (PreH10 : (id_pre = 0)) (PreH11 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH12 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH13 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskRegGet_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 0)) (PreH2 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre < 63)) (PreH8 : (id_pre = 0)) (PreH9 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH10 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH11 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (ptcb = 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_8 := OSTaskRegGet_partial_solve_wit_8_pure -> OSTaskRegGet_partial_solve_wit_8_aux.

Definition OSTaskRegGet_partial_solve_wit_9_pure := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre < 63)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskRegGet_partial_solve_wit_9_pure_split_goal_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre < 63)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskRegGet_partial_solve_wit_9_pure_split_goal_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre < 63)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskRegGet_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (ptcb = 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_9 := OSTaskRegGet_partial_solve_wit_9_pure -> OSTaskRegGet_partial_solve_wit_9_aux.

Definition OSTaskRegGet_partial_solve_wit_10_pure := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskRegGet_partial_solve_wit_10_pure_split_goal_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskRegGet_partial_solve_wit_10_pure_split_goal_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (ptcb = 1)) (PreH4 : (ptcb <> 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH8 : (0 <= prio_pre)) (PreH9 : (prio_pre <= 255)) (PreH10 : (prio_pre = 255)) (PreH11 : (id_pre = 0)) (PreH12 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH13 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH14 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskRegGet_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb = 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (ptcb = 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_10 := OSTaskRegGet_partial_solve_wit_10_pure -> OSTaskRegGet_partial_solve_wit_10_aux.

Definition OSTaskRegGet_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ”
.

Definition OSTaskRegGet_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_11 := OSTaskRegGet_partial_solve_wit_11_pure -> OSTaskRegGet_partial_solve_wit_11_aux.

Definition OSTaskRegGet_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ”
.

Definition OSTaskRegGet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (PreH1 : (ptcb <> 1)) (PreH2 : (ptcb <> 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre < 63)) (PreH9 : (id_pre = 0)) (PreH10 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH11 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH12 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_12 := OSTaskRegGet_partial_solve_wit_12_pure -> OSTaskRegGet_partial_solve_wit_12_aux.

Definition OSTaskRegGet_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (id_pre = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual )) (PreH7 : (ptcb <> 1)) (PreH8 : (ptcb <> 0)) (PreH9 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre <= 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (id_pre = 0)) (PreH16 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH17 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH18 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |-> observed)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ”
.

Definition OSTaskRegGet_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (id_pre = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual )) (PreH7 : (ptcb <> 1)) (PreH8 : (ptcb <> 0)) (PreH9 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre <= 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (id_pre = 0)) (PreH16 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH17 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH18 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry_2 prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  ((( &( "id" ) )) # UChar  |-> 0)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (0 * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_13 := OSTaskRegGet_partial_solve_wit_13_pure -> OSTaskRegGet_partial_solve_wit_13_aux.

Definition OSTaskRegGet_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (id_pre = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual )) (PreH7 : (ptcb <> 1)) (PreH8 : (ptcb <> 0)) (PreH9 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre <= 255)) (PreH14 : (prio_pre < 63)) (PreH15 : (id_pre = 0)) (PreH16 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH17 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH18 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "value" ) )) # UInt  |-> observed)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ”
.

Definition OSTaskRegGet_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (id_pre = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual )) (PreH7 : (ptcb <> 1)) (PreH8 : (ptcb <> 0)) (PreH9 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH10 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH12 : (0 <= prio_pre)) (PreH13 : (prio_pre <= 255)) (PreH14 : (prio_pre < 63)) (PreH15 : (id_pre = 0)) (PreH16 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH17 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH18 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "id" ) )) # UChar  |-> id_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id_pre * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry_2 prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  ((( &( "id" ) )) # UChar  |-> 0)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (0 * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_14 := OSTaskRegGet_partial_solve_wit_14_pure -> OSTaskRegGet_partial_solve_wit_14_aux.

Definition OSTaskRegGet_partial_solve_wit_15_pure := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (0 = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH7 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH8 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH9 : (id_pre = 0)) (PreH10 : (ptcb <> 0)) (PreH11 : (ptcb <> 1)) (PreH12 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH13 : (ptcb <> 1)) (PreH14 : (ptcb <> 0)) (PreH15 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH16 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH18 : (0 <= prio_pre)) (PreH19 : (prio_pre <= 255)) (PreH20 : (prio_pre < 63)) (PreH21 : (id_pre = 0)) (PreH22 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH23 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH24 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : (observed >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH10 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH11 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH12 : (id_pre = 0)) (PreH13 : (ptcb <> 0)) (PreH14 : (ptcb <> 1)) (PreH15 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH16 : (ptcb <> 1)) (PreH17 : (ptcb <> 0)) (PreH18 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH19 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH20 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH21 : (0 <= prio_pre)) (PreH22 : (prio_pre <= 255)) (PreH23 : (prio_pre < 63)) (PreH24 : (id_pre = 0)) (PreH25 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH26 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH27 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskRegGet_partial_solve_wit_15_pure_split_goal_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : (observed >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH10 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH11 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH12 : (id_pre = 0)) (PreH13 : (ptcb <> 0)) (PreH14 : (ptcb <> 1)) (PreH15 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH16 : (ptcb <> 1)) (PreH17 : (ptcb <> 0)) (PreH18 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH19 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH20 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH21 : (0 <= prio_pre)) (PreH22 : (prio_pre <= 255)) (PreH23 : (prio_pre < 63)) (PreH24 : (id_pre = 0)) (PreH25 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH26 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH27 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskRegGet_partial_solve_wit_15_pure_split_goal_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : (observed >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH10 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH11 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH12 : (id_pre = 0)) (PreH13 : (ptcb <> 0)) (PreH14 : (ptcb <> 1)) (PreH15 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH16 : (ptcb <> 1)) (PreH17 : (ptcb <> 0)) (PreH18 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH19 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH20 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH21 : (0 <= prio_pre)) (PreH22 : (prio_pre <= 255)) (PreH23 : (prio_pre < 63)) (PreH24 : (id_pre = 0)) (PreH25 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH26 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH27 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskRegGet_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (0 = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH7 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH8 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH9 : (id_pre = 0)) (PreH10 : (ptcb <> 0)) (PreH11 : (ptcb <> 1)) (PreH12 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH13 : (ptcb <> 1)) (PreH14 : (ptcb <> 0)) (PreH15 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH16 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH18 : (0 <= prio_pre)) (PreH19 : (prio_pre <= 255)) (PreH20 : (prio_pre < 63)) (PreH21 : (id_pre = 0)) (PreH22 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH23 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH24 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual_2 ) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 ) ” 
  &&  “ (task_reg_get_selection sg entry_3 prio_pre ptcb ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry_3 caller ptcb observed residual ) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry_2 prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_15 := OSTaskRegGet_partial_solve_wit_15_pure -> OSTaskRegGet_partial_solve_wit_15_aux.

Definition OSTaskRegGet_partial_solve_wit_16_pure := 
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (0 = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH7 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH8 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH9 : (id_pre = 0)) (PreH10 : (ptcb <> 0)) (PreH11 : (ptcb <> 1)) (PreH12 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH13 : (ptcb <> 1)) (PreH14 : (ptcb <> 0)) (PreH15 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH16 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH18 : (0 <= prio_pre)) (PreH19 : (prio_pre <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (id_pre = 0)) (PreH22 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH23 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH24 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : (observed >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH10 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH11 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH12 : (id_pre = 0)) (PreH13 : (ptcb <> 0)) (PreH14 : (ptcb <> 1)) (PreH15 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH16 : (ptcb <> 1)) (PreH17 : (ptcb <> 0)) (PreH18 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH19 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH20 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH21 : (0 <= prio_pre)) (PreH22 : (prio_pre <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (id_pre = 0)) (PreH25 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH26 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH27 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskRegGet_partial_solve_wit_16_pure_split_goal_1 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : (observed >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH10 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH11 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH12 : (id_pre = 0)) (PreH13 : (ptcb <> 0)) (PreH14 : (ptcb <> 1)) (PreH15 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH16 : (ptcb <> 1)) (PreH17 : (ptcb <> 0)) (PreH18 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH19 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH20 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH21 : (0 <= prio_pre)) (PreH22 : (prio_pre <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (id_pre = 0)) (PreH25 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH26 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH27 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskRegGet_partial_solve_wit_16_pure_split_goal_2 := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : (observed >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) (PreH9 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH10 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH11 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH12 : (id_pre = 0)) (PreH13 : (ptcb <> 0)) (PreH14 : (ptcb <> 1)) (PreH15 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH16 : (ptcb <> 1)) (PreH17 : (ptcb <> 0)) (PreH18 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH19 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH20 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH21 : (0 <= prio_pre)) (PreH22 : (prio_pre <= 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (id_pre = 0)) (PreH25 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH26 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH27 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "id" ) )) # UChar  |-> 0)
  **  ((( &( "value" ) )) # UInt  |-> observed)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskRegGet_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (id_pre: Z) (prio_pre: Z) (X: (Z -> (Z -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (observed: Z) (residual: Assertion) (entry_3: UCOS2_Verify_State) (residual_2: Assertion) (entry: UCOS2_Verify_State) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_reg_get_selection sg entry prio_pre ptcb )) (PreH3 : (0 = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry caller ptcb observed residual_2 )) (PreH7 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 )) (PreH8 : (task_reg_get_selection sg entry_3 prio_pre ptcb )) (PreH9 : (id_pre = 0)) (PreH10 : (ptcb <> 0)) (PreH11 : (ptcb <> 1)) (PreH12 : (task_reg_get_word_view sg entry_3 caller ptcb observed residual )) (PreH13 : (ptcb <> 1)) (PreH14 : (ptcb <> 0)) (PreH15 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH16 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_reg_get_admission critical sg invocation before caller prio_pre id_pre )) (PreH18 : (0 <= prio_pre)) (PreH19 : (prio_pre <= 255)) (PreH20 : (prio_pre = 255)) (PreH21 : (id_pre = 0)) (PreH22 : (task_reg_get_scalar_valid prio_pre id_pre )) (PreH23 : (task_reg_get_selection sg entry_2 prio_pre ptcb )) (PreH24 : (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio_pre ptcb ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual_2 ) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_3 ) ” 
  &&  “ (task_reg_get_selection sg entry_3 prio_pre ptcb ) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry_3 caller ptcb observed residual ) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_admission critical sg invocation before caller prio_pre id_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (id_pre = 0) ” 
  &&  “ (task_reg_get_scalar_valid prio_pre id_pre ) ” 
  &&  “ (task_reg_get_selection sg entry_2 prio_pre ptcb ) ” 
  &&  “ (task_reg_get_safe critical sg invocation before caller prio_pre id_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskRegGet_partial_solve_wit_16 := OSTaskRegGet_partial_solve_wit_16_pure -> OSTaskRegGet_partial_solve_wit_16_aux.

Definition OSTaskRegGet_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (prio = 255)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (prio = 255) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  (task_reg_get_current_frame sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (prio = 255)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (prio = 255) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry)))
  **  (task_reg_get_current_frame sg entry )
).

Definition OSTaskRegGet_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (prio = 255)) (PreH4 : (ptcb = (task_reg_get_current_pointer (sg) (entry_2)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry_2)))
  **  (task_reg_get_current_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (prio = 255)) (PreH4 : (ptcb = (task_reg_get_current_pointer (sg) (entry_2)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_reg_get_current_pointer (sg) (entry_2)))
  **  (task_reg_get_current_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
).

Definition OSTaskRegGet_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 63)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 63) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry) (prio)))
  **  (task_reg_get_table_frame sg entry prio )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 63)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 63) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry) (prio)))
  **  (task_reg_get_table_frame sg entry prio )
).

Definition OSTaskRegGet_which_implies_wit_4 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 63)) (PreH5 : (ptcb = (task_reg_get_table_pointer (sg) (entry_2) (prio)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry_2) (prio)))
  **  (task_reg_get_table_frame sg entry_2 prio )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 63)) (PreH5 : (ptcb = (task_reg_get_table_pointer (sg) (entry_2) (prio)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_reg_get_table_pointer (sg) (entry_2) (prio)))
  **  (task_reg_get_table_frame sg entry_2 prio )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
).

Definition OSTaskRegGet_which_implies_wit_5 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_admission critical sg invocation before caller prio id )) (PreH3 : (task_reg_get_scalar_valid prio id )) (PreH4 : (task_reg_get_selection sg entry_2 prio ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (observed: Z)  (residual: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ” 
  &&  “ (id = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (id: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_admission critical sg invocation before caller prio id )) (PreH3 : (task_reg_get_scalar_valid prio id )) (PreH4 : (task_reg_get_selection sg entry_2 prio ptcb )) (PreH5 : (ptcb <> 0)) (PreH6 : (ptcb <> 1)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (caller )
|--
  EX (observed: Z)  (residual: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ” 
  &&  “ (id = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual )
).

Definition OSTaskRegGet_which_implies_wit_6 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (residual_2: Assertion) (observed: Z) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (prio: Z) (id: Z) (PreH1 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH2 : (task_reg_get_selection sg entry_2 prio ptcb )) (PreH3 : (id = 0)) (PreH4 : (ptcb <> 0)) (PreH5 : (ptcb <> 1)) (PreH6 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual_2 )
|--
  EX (residual: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ” 
  &&  “ (id = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (residual_2: Assertion) (observed: Z) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (prio: Z) (id: Z) (PreH1 : (observed <= UINT_MAX)) (PreH2 : (observed >= 0)) (PreH3 : (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry_2 )) (PreH4 : (task_reg_get_selection sg entry_2 prio ptcb )) (PreH5 : (id = 0)) (PreH6 : (ptcb <> 0)) (PreH7 : (ptcb <> 1)) (PreH8 : (task_reg_get_word_view sg entry_2 caller ptcb observed residual_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (id * sizeof(UINT)))) # UInt  |-> observed)
  **  (task_reg_get_read_frame ptcb observed residual_2 )
|--
  EX (residual: Assertion)  (entry: UCOS2_Verify_State) ,
  “ (task_reg_get_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_reg_get_selection sg entry prio ptcb ) ” 
  &&  “ (id = 0) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_reg_get_word_view sg entry caller ptcb observed residual ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
).

Module Type VC_Correct.


Axiom proof_of_OSTaskRegGet_safety_wit_1 : OSTaskRegGet_safety_wit_1.
Axiom proof_of_OSTaskRegGet_safety_wit_2 : OSTaskRegGet_safety_wit_2.
Axiom proof_of_OSTaskRegGet_safety_wit_3 : OSTaskRegGet_safety_wit_3.
Axiom proof_of_OSTaskRegGet_safety_wit_4 : OSTaskRegGet_safety_wit_4.
Axiom proof_of_OSTaskRegGet_safety_wit_5 : OSTaskRegGet_safety_wit_5.
Axiom proof_of_OSTaskRegGet_safety_wit_6 : OSTaskRegGet_safety_wit_6.
Axiom proof_of_OSTaskRegGet_safety_wit_7 : OSTaskRegGet_safety_wit_7.
Axiom proof_of_OSTaskRegGet_safety_wit_8 : OSTaskRegGet_safety_wit_8.
Axiom proof_of_OSTaskRegGet_safety_wit_9 : OSTaskRegGet_safety_wit_9.
Axiom proof_of_OSTaskRegGet_safety_wit_10 : OSTaskRegGet_safety_wit_10.
Axiom proof_of_OSTaskRegGet_safety_wit_11 : OSTaskRegGet_safety_wit_11.
Axiom proof_of_OSTaskRegGet_safety_wit_12 : OSTaskRegGet_safety_wit_12.
Axiom proof_of_OSTaskRegGet_safety_wit_13 : OSTaskRegGet_safety_wit_13.
Axiom proof_of_OSTaskRegGet_safety_wit_14 : OSTaskRegGet_safety_wit_14.
Axiom proof_of_OSTaskRegGet_entail_wit_1_1 : OSTaskRegGet_entail_wit_1_1.
Axiom proof_of_OSTaskRegGet_entail_wit_1_2 : OSTaskRegGet_entail_wit_1_2.
Axiom proof_of_OSTaskRegGet_entail_wit_2_1 : OSTaskRegGet_entail_wit_2_1.
Axiom proof_of_OSTaskRegGet_entail_wit_2_2 : OSTaskRegGet_entail_wit_2_2.
Axiom proof_of_OSTaskRegGet_return_wit_1 : OSTaskRegGet_return_wit_1.
Axiom proof_of_OSTaskRegGet_return_wit_2 : OSTaskRegGet_return_wit_2.
Axiom proof_of_OSTaskRegGet_return_wit_3 : OSTaskRegGet_return_wit_3.
Axiom proof_of_OSTaskRegGet_return_wit_4 : OSTaskRegGet_return_wit_4.
Axiom proof_of_OSTaskRegGet_return_wit_5 : OSTaskRegGet_return_wit_5.
Axiom proof_of_OSTaskRegGet_return_wit_6 : OSTaskRegGet_return_wit_6.
Axiom proof_of_OSTaskRegGet_return_wit_7 : OSTaskRegGet_return_wit_7.
Axiom proof_of_OSTaskRegGet_return_wit_8 : OSTaskRegGet_return_wit_8.
Axiom proof_of_OSTaskRegGet_return_wit_9 : OSTaskRegGet_return_wit_9.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_1_pure : OSTaskRegGet_partial_solve_wit_1_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_1 : OSTaskRegGet_partial_solve_wit_1.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_2_pure : OSTaskRegGet_partial_solve_wit_2_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_2 : OSTaskRegGet_partial_solve_wit_2.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_3_pure : OSTaskRegGet_partial_solve_wit_3_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_3 : OSTaskRegGet_partial_solve_wit_3.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_4_pure : OSTaskRegGet_partial_solve_wit_4_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_4 : OSTaskRegGet_partial_solve_wit_4.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_5_pure : OSTaskRegGet_partial_solve_wit_5_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_5 : OSTaskRegGet_partial_solve_wit_5.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_6_pure : OSTaskRegGet_partial_solve_wit_6_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_6 : OSTaskRegGet_partial_solve_wit_6.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_7_pure : OSTaskRegGet_partial_solve_wit_7_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_7 : OSTaskRegGet_partial_solve_wit_7.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_8_pure : OSTaskRegGet_partial_solve_wit_8_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_8 : OSTaskRegGet_partial_solve_wit_8.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_9_pure : OSTaskRegGet_partial_solve_wit_9_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_9 : OSTaskRegGet_partial_solve_wit_9.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_10_pure : OSTaskRegGet_partial_solve_wit_10_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_10 : OSTaskRegGet_partial_solve_wit_10.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_11_pure : OSTaskRegGet_partial_solve_wit_11_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_11 : OSTaskRegGet_partial_solve_wit_11.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_12_pure : OSTaskRegGet_partial_solve_wit_12_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_12 : OSTaskRegGet_partial_solve_wit_12.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_13_pure : OSTaskRegGet_partial_solve_wit_13_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_13 : OSTaskRegGet_partial_solve_wit_13.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_14_pure : OSTaskRegGet_partial_solve_wit_14_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_14 : OSTaskRegGet_partial_solve_wit_14.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_15_pure : OSTaskRegGet_partial_solve_wit_15_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_15 : OSTaskRegGet_partial_solve_wit_15.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_16_pure : OSTaskRegGet_partial_solve_wit_16_pure.
Axiom proof_of_OSTaskRegGet_partial_solve_wit_16 : OSTaskRegGet_partial_solve_wit_16.
Axiom proof_of_OSTaskRegGet_which_implies_wit_1 : OSTaskRegGet_which_implies_wit_1.
Axiom proof_of_OSTaskRegGet_which_implies_wit_2 : OSTaskRegGet_which_implies_wit_2.
Axiom proof_of_OSTaskRegGet_which_implies_wit_3 : OSTaskRegGet_which_implies_wit_3.
Axiom proof_of_OSTaskRegGet_which_implies_wit_4 : OSTaskRegGet_which_implies_wit_4.
Axiom proof_of_OSTaskRegGet_which_implies_wit_5 : OSTaskRegGet_which_implies_wit_5.
Axiom proof_of_OSTaskRegGet_which_implies_wit_6 : OSTaskRegGet_which_implies_wit_6.

End VC_Correct.
