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
Require Import Ucos2Verify.VC.code.task.spec.task_stk_chk_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskStkChk -----*)

Definition OSTaskStkChk_safety_wit_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <= 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_stk_chk_configuration sg )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH8 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_3 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH4 : (p_stk_data_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (task_stk_chk_configuration sg )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH13 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (caller )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_4 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH4 : (p_stk_data_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (caller )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_5 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre <= 63)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition OSTaskStkChk_safety_wit_6 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition OSTaskStkChk_safety_wit_7 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (0 <= prio)) (PreH3 : (prio <= 63)) (PreH4 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH14 : (0 <= prio)) (PreH15 : (prio <= 63)) (PreH16 : (p_stk_data_pre <> 0)) (PreH17 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_8 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_9 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_stk_chk_configuration sg )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (p_stk_data_pre <> 0)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskStkChk_safety_wit_10 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_11 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_12 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (critical_region_interval critical sg invocation entry after )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH5 : (0 <= (task_stk_chk_node_size (node)))) (PreH6 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH9 : (0 <= (task_stk_chk_node_size (node)))) (PreH10 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= (task_stk_chk_node_size (node)))) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH19 : (cpu_sr <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : ((task_stk_chk_node_size (node)) >= 0)) (PreH22 : (cpu_sr >= 0)) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH27 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH28 : (task_stk_chk_configuration sg )) (PreH29 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH30 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH31 : (0 <= prio)) (PreH32 : (prio <= 63)) (PreH33 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH34 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH35 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH36 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH37 : (0 <= prio)) (PreH38 : (prio <= 63)) (PreH39 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH40 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH41 : (0 <= prio)) (PreH42 : (prio <= 63)) (PreH43 : (task_stk_chk_configuration sg )) (PreH44 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH45 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH46 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH47 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH48 : (0 <= prio)) (PreH49 : (prio <= 63)) (PreH50 : (p_stk_data_pre <> 0)) (PreH51 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_safety_wit_13 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (size_2: Z) (pchk_2: Z) (index: Z) (cpu_sr_2: Z) (prio_2: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH2 : (0 <= index)) (PreH3 : (index <= (task_stk_chk_count (count)))) (PreH4 : (pchk_2 = (task_stk_chk_cursor (snapshot) (index)))) (PreH5 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH6 : (0 <= size_2)) (PreH7 : (size_2 <= UINT_MAX)) (PreH8 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH9 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH10 : (pchk = (task_stk_chk_cursor (snapshot) (0)))) (PreH11 : (nfree = 0)) (PreH12 : (size = (task_stk_chk_size (snapshot)))) (PreH13 : (0 <= size)) (PreH14 : (size <= UINT_MAX)) (PreH15 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk_2) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_2)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_2)
  **  ((( &( "pchk" ) )) # Ptr  |-> pchk_2)
  **  ((( &( "nfree" ) )) # UInt  |-> index)
  **  ((( &( "size" ) )) # UInt  |-> size_2)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskStkChk_entail_wit_1_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH4 : (p_stk_data_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre <= 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (task_stk_chk_configuration sg )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH13 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (caller )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_entail_wit_1_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask retval before entry_2 )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH4 : (p_stk_data_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (caller )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask retval before entry ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_entail_wit_2_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre selected )) (PreH3 : (0 <= selected)) (PreH4 : (selected <= 63)) (PreH5 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_configuration sg )) (PreH8 : (prio_pre = 255)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_self_view sg entry caller p_stk_data_pre selected residual )) (PreH12 : (prio_pre = 255)) (PreH13 : (task_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH16 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (0 <= prio_pre)) (PreH18 : (prio_pre <= 255)) (PreH19 : (prio_pre = 255)) (PreH20 : (p_stk_data_pre <> 0)) (PreH21 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre selected ) ” 
  &&  “ (0 <= selected) ” 
  &&  “ (selected <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_entail_wit_2_2 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre <= 63)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio_pre ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre <= 63)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  TT && emp 
|--
  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio_pre ) ”
  &&  emp
).

Definition OSTaskStkChk_entail_wit_2_2_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre <= 63)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio_pre )
.

Definition OSTaskStkChk_entail_wit_3 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = 0)) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_stk_chk_configuration sg )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (p_stk_data_pre <> 0)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = 0)) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH14 : (0 <= prio)) (PreH15 : (prio <= 63)) (PreH16 : (p_stk_data_pre <> 0)) (PreH17 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  TT && emp 
|--
  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 ) ”
  &&  emp
).

Definition OSTaskStkChk_entail_wit_3_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = 0)) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH14 : (0 <= prio)) (PreH15 : (prio <= 63)) (PreH16 : (p_stk_data_pre <> 0)) (PreH17 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )
.

Definition OSTaskStkChk_entail_wit_4 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_stk_chk_configuration sg )) (PreH12 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH14 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH15 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (p_stk_data_pre <> 0)) (PreH19 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_stk_chk_configuration sg )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (p_stk_data_pre <> 0)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  TT && emp 
|--
  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 ) ”
  &&  emp
).

Definition OSTaskStkChk_entail_wit_4_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 63)) (PreH10 : (task_stk_chk_configuration sg )) (PreH11 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (p_stk_data_pre <> 0)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )
.

Definition OSTaskStkChk_entail_wit_5 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((Z.land (task_stk_chk_node_option (node)) 1) = 0)) (PreH4 : (task_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH10 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH11 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio)) (PreH14 : (prio <= 63)) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH24 : (0 <= prio)) (PreH25 : (prio <= 63)) (PreH26 : (p_stk_data_pre <> 0)) (PreH27 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((Z.land (task_stk_chk_node_option (node)) 1) = 0)) (PreH4 : (task_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH10 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH11 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio)) (PreH14 : (prio <= 63)) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH24 : (0 <= prio)) (PreH25 : (prio <= 63)) (PreH26 : (p_stk_data_pre <> 0)) (PreH27 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  TT && emp 
|--
  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 ) ”
  &&  emp
).

Definition OSTaskStkChk_entail_wit_5_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((Z.land (task_stk_chk_node_option (node)) 1) = 0)) (PreH4 : (task_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH10 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH11 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio)) (PreH14 : (prio <= 63)) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH24 : (0 <= prio)) (PreH25 : (prio <= 63)) (PreH26 : (p_stk_data_pre <> 0)) (PreH27 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )
.

Definition OSTaskStkChk_entail_wit_6 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH5 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH12 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH13 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH14 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH18 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (0 <= prio)) (PreH20 : (prio <= 63)) (PreH21 : (task_stk_chk_configuration sg )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH23 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH24 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH25 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH26 : (0 <= prio)) (PreH27 : (prio <= 63)) (PreH28 : (p_stk_data_pre <> 0)) (PreH29 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
|--
  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (cpu_sr <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((task_stk_chk_node_size (node)) >= 0) ” 
  &&  “ (cpu_sr >= 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
.

Definition OSTaskStkChk_entail_wit_7 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH5 : (0 <= (task_stk_chk_node_size (node)))) (PreH6 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH9 : (0 <= (task_stk_chk_node_size (node)))) (PreH10 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= (task_stk_chk_node_size (node)))) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH19 : (cpu_sr <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : ((task_stk_chk_node_size (node)) >= 0)) (PreH22 : (cpu_sr >= 0)) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH27 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH28 : (task_stk_chk_configuration sg )) (PreH29 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH30 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH31 : (0 <= prio)) (PreH32 : (prio <= 63)) (PreH33 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH34 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH35 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH36 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH37 : (0 <= prio)) (PreH38 : (prio <= 63)) (PreH39 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH40 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH41 : (0 <= prio)) (PreH42 : (prio <= 63)) (PreH43 : (task_stk_chk_configuration sg )) (PreH44 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH45 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH46 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH47 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH48 : (0 <= prio)) (PreH49 : (prio <= 63)) (PreH50 : (p_stk_data_pre <> 0)) (PreH51 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (after: UCOS2_Verify_State)  (snapshot: TaskStackCheckSnapshot)  (region: TaskStackRegion)  (words: TaskStkChkWords)  (count: nat)  (stop: Z)  (residual: Assertion) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (snapshot = (task_stk_chk_node_snapshot (slot) (node))) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_size (snapshot))) ” 
  &&  “ ((task_stk_chk_node_bottom (node)) = (task_stk_chk_bottom (snapshot))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH5 : (0 <= (task_stk_chk_node_size (node)))) (PreH6 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH9 : (0 <= (task_stk_chk_node_size (node)))) (PreH10 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= (task_stk_chk_node_size (node)))) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH19 : (cpu_sr <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : ((task_stk_chk_node_size (node)) >= 0)) (PreH22 : (cpu_sr >= 0)) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH27 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH28 : (task_stk_chk_configuration sg )) (PreH29 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH30 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH31 : (0 <= prio)) (PreH32 : (prio <= 63)) (PreH33 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH34 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH35 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH36 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH37 : (0 <= prio)) (PreH38 : (prio <= 63)) (PreH39 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH40 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH41 : (0 <= prio)) (PreH42 : (prio <= 63)) (PreH43 : (task_stk_chk_configuration sg )) (PreH44 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH45 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH46 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH47 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH48 : (0 <= prio)) (PreH49 : (prio <= 63)) (PreH50 : (p_stk_data_pre <> 0)) (PreH51 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (after: UCOS2_Verify_State)  (region: TaskStackRegion)  (words: TaskStkChkWords)  (count: nat)  (stop: Z)  (residual: Assertion) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio (task_stk_chk_node_snapshot (slot) (node)) region words count stop residual ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_size ((task_stk_chk_node_snapshot (slot) (node))))) ” 
  &&  “ ((task_stk_chk_node_bottom (node)) = (task_stk_chk_bottom ((task_stk_chk_node_snapshot (slot) (node))))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
).

Definition OSTaskStkChk_entail_wit_8 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (prio: Z) (cpu_sr: Z) (ptcb: Z) (size: Z) (pchk: Z) (nfree: Z) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : ((task_stk_chk_bottom (snapshot)) = (task_stk_chk_cursor (snapshot) (0)))) (PreH3 : ((task_stk_chk_size (snapshot)) = (task_stk_chk_size (snapshot)))) (PreH4 : (0 = 0)) (PreH5 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH6 : (snapshot = (task_stk_chk_node_snapshot (slot) (node)))) (PreH7 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH8 : (size = (task_stk_chk_size (snapshot)))) (PreH9 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH10 : (0 <= size)) (PreH11 : (size <= UINT_MAX)) (PreH12 : (nfree = 0)) (PreH13 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (((task_stk_chk_cursor (snapshot) (0))) # UInt  |-> (task_stk_chk_word (count) (stop) (0)))
  **  (task_stk_chk_scan_read_frame region words 0 residual )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ ((task_stk_chk_bottom (snapshot)) = (task_stk_chk_cursor (snapshot) (0))) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((task_stk_chk_size (snapshot)) = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= (task_stk_chk_size (snapshot))) ” 
  &&  “ ((task_stk_chk_size (snapshot)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (0))) # UInt  |-> (task_stk_chk_word (count) (stop) (0)))
  **  (task_stk_chk_scan_read_frame region words 0 residual )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
.

Definition OSTaskStkChk_entail_wit_9 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (pchk = (task_stk_chk_cursor (snapshot) (0)))) (PreH3 : (nfree = 0)) (PreH4 : (size = (task_stk_chk_size (snapshot)))) (PreH5 : (0 <= size)) (PreH6 : (size <= UINT_MAX)) (PreH7 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (0))) # UInt  |-> (task_stk_chk_word (count) (stop) (0)))
  **  (task_stk_chk_scan_read_frame region words 0 residual )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= nfree) ” 
  &&  “ (nfree <= (task_stk_chk_count (count))) ” 
  &&  “ (pchk = (task_stk_chk_cursor (snapshot) (nfree))) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (pchk = (task_stk_chk_cursor (snapshot) (0))) ” 
  &&  “ (nfree = 0) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (nfree))) # UInt  |-> (task_stk_chk_word (count) (stop) (nfree)))
  **  (task_stk_chk_scan_read_frame region words nfree residual )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (0)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (0)) >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (pchk = (task_stk_chk_cursor (snapshot) (0)))) (PreH5 : (nfree = 0)) (PreH6 : (size = (task_stk_chk_size (snapshot)))) (PreH7 : (0 <= size)) (PreH8 : (size <= UINT_MAX)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  TT && emp 
|--
  “ (0 <= (task_stk_chk_count (count))) ”
  &&  emp
).

Definition OSTaskStkChk_entail_wit_9_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (0)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (0)) >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (pchk = (task_stk_chk_cursor (snapshot) (0)))) (PreH5 : (nfree = 0)) (PreH6 : (size = (task_stk_chk_size (snapshot)))) (PreH7 : (0 <= size)) (PreH8 : (size <= UINT_MAX)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (0 <= (task_stk_chk_count (count)))
.

Definition OSTaskStkChk_entail_wit_10 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) = 0)) (PreH2 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH3 : (0 <= index)) (PreH4 : (index <= (task_stk_chk_count (count)))) (PreH5 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH6 : (size = (task_stk_chk_size (snapshot)))) (PreH7 : (0 <= size)) (PreH8 : (size <= UINT_MAX)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH10 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH11 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH12 : (nfree = 0)) (PreH13 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH14 : (0 <= size_2)) (PreH15 : (size_2 <= UINT_MAX)) (PreH16 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  EX (previous: Z) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= previous) ” 
  &&  “ (previous < (task_stk_chk_count (count))) ” 
  &&  “ ((pchk + (1 * sizeof(UINT))) = ((task_stk_chk_cursor (snapshot) (previous)) + 4 )) ” 
  &&  “ ((unsigned_last_nbits ((index + 1 )) (32)) = (previous + 1 )) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (index)) >= 0)) (PreH3 : ((task_stk_chk_word (count) (stop) (index)) = 0)) (PreH4 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH5 : (0 <= index)) (PreH6 : (index <= (task_stk_chk_count (count)))) (PreH7 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH8 : (size = (task_stk_chk_size (snapshot)))) (PreH9 : (0 <= size)) (PreH10 : (size <= UINT_MAX)) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH12 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH13 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH14 : (nfree = 0)) (PreH15 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH16 : (0 <= size_2)) (PreH17 : (size_2 <= UINT_MAX)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  EX (previous: Z) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= previous) ” 
  &&  “ (previous < (task_stk_chk_count (count))) ” 
  &&  “ ((pchk + (1 * sizeof(UINT))) = ((task_stk_chk_cursor (snapshot) (previous)) + 4 )) ” 
  &&  “ ((unsigned_last_nbits ((index + 1 )) (32)) = (previous + 1 )) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
).

Definition OSTaskStkChk_entail_wit_11 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree_2: Z) (size_2: Z) (previous: Z) (index: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH2 : (0 <= index)) (PreH3 : (index <= (task_stk_chk_count (count)))) (PreH4 : (((task_stk_chk_cursor (snapshot) (previous)) + 4 ) = (task_stk_chk_cursor (snapshot) (index)))) (PreH5 : ((previous + 1 ) = index)) (PreH6 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH7 : (0 <= previous)) (PreH8 : (previous < (task_stk_chk_count (count)))) (PreH9 : (pchk_2 = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH10 : (nfree_2 = (previous + 1 ))) (PreH11 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH12 : (0 <= size_2)) (PreH13 : (size_2 <= UINT_MAX)) (PreH14 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (((task_stk_chk_cursor (snapshot) (index))) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (task_stk_chk_scan_read_frame region words index residual )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (size: Z)  (nfree: Z)  (pchk: Z)  (cpu_sr: Z)  (prio: Z) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual ) ” 
  &&  “ (0 <= (previous + 1 )) ” 
  &&  “ ((previous + 1 ) <= (task_stk_chk_count (count))) ” 
  &&  “ (((task_stk_chk_cursor (snapshot) (previous)) + 4 ) = (task_stk_chk_cursor (snapshot) ((previous + 1 )))) ” 
  &&  “ (size_2 = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size_2) ” 
  &&  “ (size_2 <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (pchk = (task_stk_chk_cursor (snapshot) (0))) ” 
  &&  “ (nfree = 0) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((previous + 1 )))) # UInt  |-> (task_stk_chk_word (count) (stop) ((previous + 1 ))))
  **  (task_stk_chk_scan_read_frame region words (previous + 1 ) residual )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree_2: Z) (size_2: Z) (previous: Z) (index: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (index)) >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH4 : (0 <= index)) (PreH5 : (index <= (task_stk_chk_count (count)))) (PreH6 : (((task_stk_chk_cursor (snapshot) (previous)) + 4 ) = (task_stk_chk_cursor (snapshot) (index)))) (PreH7 : ((previous + 1 ) = index)) (PreH8 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH9 : (0 <= previous)) (PreH10 : (previous < (task_stk_chk_count (count)))) (PreH11 : (pchk_2 = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH12 : (nfree_2 = (previous + 1 ))) (PreH13 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH14 : (0 <= size_2)) (PreH15 : (size_2 <= UINT_MAX)) (PreH16 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (((task_stk_chk_cursor (snapshot) (index))) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (task_stk_chk_scan_read_frame region words index residual )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (cpu_sr: Z)  (prio: Z) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual ) ” 
  &&  “ (0 <= (previous + 1 )) ” 
  &&  “ ((previous + 1 ) <= (task_stk_chk_count (count))) ” 
  &&  “ (((task_stk_chk_cursor (snapshot) (previous)) + 4 ) = (task_stk_chk_cursor (snapshot) ((previous + 1 )))) ” 
  &&  “ (size_2 = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size_2) ” 
  &&  “ (size_2 <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= (task_stk_chk_size (snapshot))) ” 
  &&  “ ((task_stk_chk_size (snapshot)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((previous + 1 )))) # UInt  |-> (task_stk_chk_word (count) (stop) ((previous + 1 ))))
  **  (task_stk_chk_scan_read_frame region words (previous + 1 ) residual )
).

Definition OSTaskStkChk_entail_wit_12 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <> 0)) (PreH2 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH3 : (0 <= index)) (PreH4 : (index <= (task_stk_chk_count (count)))) (PreH5 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH6 : (size = (task_stk_chk_size (snapshot)))) (PreH7 : (0 <= size)) (PreH8 : (size <= UINT_MAX)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH10 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH11 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH12 : (nfree = 0)) (PreH13 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH14 : (0 <= size_2)) (PreH15 : (size_2 <= UINT_MAX)) (PreH16 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (index = (task_stk_chk_count (count))) ” 
  &&  “ ((pchk + (1 * sizeof(UINT))) = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (index)) >= 0)) (PreH3 : ((task_stk_chk_word (count) (stop) (index)) <> 0)) (PreH4 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH5 : (0 <= index)) (PreH6 : (index <= (task_stk_chk_count (count)))) (PreH7 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH8 : (size = (task_stk_chk_size (snapshot)))) (PreH9 : (0 <= size)) (PreH10 : (size <= UINT_MAX)) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH12 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH13 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH14 : (nfree = 0)) (PreH15 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH16 : (0 <= size_2)) (PreH17 : (size_2 <= UINT_MAX)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  “ ((pchk + (1 * sizeof(UINT))) = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ” 
  &&  “ (index = (task_stk_chk_count (count))) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
).

Definition OSTaskStkChk_entail_wit_12_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (index)) >= 0)) (PreH3 : ((task_stk_chk_word (count) (stop) (index)) <> 0)) (PreH4 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH5 : (0 <= index)) (PreH6 : (index <= (task_stk_chk_count (count)))) (PreH7 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH8 : (size = (task_stk_chk_size (snapshot)))) (PreH9 : (0 <= size)) (PreH10 : (size <= UINT_MAX)) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH12 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH13 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH14 : (nfree = 0)) (PreH15 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH16 : (0 <= size_2)) (PreH17 : (size_2 <= UINT_MAX)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  “ ((pchk + (1 * sizeof(UINT))) = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ”
.

Definition OSTaskStkChk_entail_wit_12_split_goal_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (index)) >= 0)) (PreH3 : ((task_stk_chk_word (count) (stop) (index)) <> 0)) (PreH4 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH5 : (0 <= index)) (PreH6 : (index <= (task_stk_chk_count (count)))) (PreH7 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH8 : (size = (task_stk_chk_size (snapshot)))) (PreH9 : (0 <= size)) (PreH10 : (size <= UINT_MAX)) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH12 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH13 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH14 : (nfree = 0)) (PreH15 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH16 : (0 <= size_2)) (PreH17 : (size_2 <= UINT_MAX)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  “ (index = (task_stk_chk_count (count))) ”
.

Definition OSTaskStkChk_entail_wit_12_split_goal_spatial := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio_2: Z) (cpu_sr_2: Z) (pchk_2: Z) (nfree: Z) (size_2: Z) (size: Z) (pchk: Z) (index: Z) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (index)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (index)) >= 0)) (PreH3 : ((task_stk_chk_word (count) (stop) (index)) <> 0)) (PreH4 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH5 : (0 <= index)) (PreH6 : (index <= (task_stk_chk_count (count)))) (PreH7 : (pchk = (task_stk_chk_cursor (snapshot) (index)))) (PreH8 : (size = (task_stk_chk_size (snapshot)))) (PreH9 : (0 <= size)) (PreH10 : (size <= UINT_MAX)) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH12 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH13 : (pchk_2 = (task_stk_chk_cursor (snapshot) (0)))) (PreH14 : (nfree = 0)) (PreH15 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH16 : (0 <= size_2)) (PreH17 : (size_2 <= UINT_MAX)) (PreH18 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((pchk) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
.

Definition OSTaskStkChk_return_wit_1 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (nfree: Z) (pchk: Z) (size: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after_2 prio snapshot region words count stop residual )) (PreH2 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after_2 prio snapshot region words count stop residual )) (PreH3 : (nfree = (task_stk_chk_count (count)))) (PreH4 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) (PreH5 : (size = (task_stk_chk_size (snapshot)))) (PreH6 : (0 <= size)) (PreH7 : (size <= UINT_MAX)) (PreH8 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> (task_stk_chk_count (count)))
  **  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> (unsigned_last_nbits ((size - (task_stk_chk_count (count)) )) (32)))
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (0 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (nfree: Z) (pchk: Z) (size: Z) (PreH1 : ((unsigned_last_nbits ((size - (task_stk_chk_count (count)) )) (32)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_count (count)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((size - (task_stk_chk_count (count)) )) (32)) >= 0)) (PreH4 : ((task_stk_chk_count (count)) >= 0)) (PreH5 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after_2 prio snapshot region words count stop residual )) (PreH6 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after_2 prio snapshot region words count stop residual )) (PreH7 : (nfree = (task_stk_chk_count (count)))) (PreH8 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) (PreH9 : (size = (task_stk_chk_size (snapshot)))) (PreH10 : (0 <= size)) (PreH11 : (size <= UINT_MAX)) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> (task_stk_chk_count (count)))
  **  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> (unsigned_last_nbits ((size - (task_stk_chk_count (count)) )) (32)))
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 0 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_return_wit_2 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (69 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 69 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_return_wit_3 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (67 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 67 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_return_wit_4 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (67 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (after_2: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after_2 )) (PreH2 : (critical_region_interval critical sg invocation entry after_2 )) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 67 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_return_wit_5 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (9 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 9 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_return_wit_6 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (9 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 9 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_return_wit_7 := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  EX (error: Z)  (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre error data after X ) ” 
  &&  “ (42 = error) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (task_stk_chk_post critical sg invocation mask before caller prio_pre p_stk_data_pre 42 data after X ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post p_stk_data_pre data )
).

Definition OSTaskStkChk_partial_solve_wit_1_pure := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ”
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_stk_chk_configuration sg )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ”
).

Definition OSTaskStkChk_partial_solve_wit_1_pure_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_stk_chk_configuration sg )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ”
.

Definition OSTaskStkChk_partial_solve_wit_1_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (task_stk_chk_configuration sg )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
.

Definition OSTaskStkChk_partial_solve_wit_1 := OSTaskStkChk_partial_solve_wit_1_pure -> OSTaskStkChk_partial_solve_wit_1_aux.

Definition OSTaskStkChk_partial_solve_wit_2_pure := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_valid_arguments 255 p_stk_data_pre ) ”
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_valid_arguments 255 p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_valid_arguments 255 p_stk_data_pre ) ”
).

Definition OSTaskStkChk_partial_solve_wit_2_pure_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_valid_arguments 255 p_stk_data_pre ) ”
.

Definition OSTaskStkChk_partial_solve_wit_2_pure_split_goal_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_valid_arguments 255 p_stk_data_pre ) ”
.

Definition OSTaskStkChk_partial_solve_wit_2_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_stk_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre <= 255)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_valid_arguments 255 p_stk_data_pre ) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (task_stk_chk_output_pre sg prio_pre p_stk_data_pre )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
.

Definition OSTaskStkChk_partial_solve_wit_2 := OSTaskStkChk_partial_solve_wit_2_pure -> OSTaskStkChk_partial_solve_wit_2_aux.

Definition OSTaskStkChk_partial_solve_wit_3 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_stk_chk_configuration sg )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
.

Definition OSTaskStkChk_partial_solve_wit_4 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data_pre)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
.

Definition OSTaskStkChk_partial_solve_wit_5_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTaskStkChk_partial_solve_wit_5_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (caller )
.

Definition OSTaskStkChk_partial_solve_wit_5 := OSTaskStkChk_partial_solve_wit_5_pure -> OSTaskStkChk_partial_solve_wit_5_aux.

Definition OSTaskStkChk_partial_solve_wit_6_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_stk_chk_configuration sg )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTaskStkChk_partial_solve_wit_6_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio_pre p_stk_data_pre )) (PreH3 : (p_stk_data_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (task_stk_chk_configuration sg )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH11 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio_pre p_stk_data_pre ) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (caller )
.

Definition OSTaskStkChk_partial_solve_wit_6 := OSTaskStkChk_partial_solve_wit_6_pure -> OSTaskStkChk_partial_solve_wit_6_aux.

Definition OSTaskStkChk_partial_solve_wit_7_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskStkChk_partial_solve_wit_7_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre <= 255)) (PreH8 : (prio_pre = 255)) (PreH9 : (p_stk_data_pre <> 0)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
.

Definition OSTaskStkChk_partial_solve_wit_7 := OSTaskStkChk_partial_solve_wit_7_pure -> OSTaskStkChk_partial_solve_wit_7_aux.

Definition OSTaskStkChk_partial_solve_wit_8_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (PreH1 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_stk_chk_configuration sg )) (PreH4 : (prio_pre = 255)) (PreH5 : (p_stk_data_pre <> 0)) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stk_chk_self_view sg entry caller p_stk_data_pre selected residual )) (PreH8 : (prio_pre = 255)) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio_pre)) (PreH14 : (prio_pre <= 255)) (PreH15 : (prio_pre = 255)) (PreH16 : (p_stk_data_pre <> 0)) (PreH17 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
  **  ((( &( "prio" ) )) # UChar  |-> selected)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_self_view sg entry caller p_stk_data_pre selected residual ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (prio_pre = 255) ”
.

Definition OSTaskStkChk_partial_solve_wit_8_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (PreH1 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_stk_chk_configuration sg )) (PreH4 : (prio_pre = 255)) (PreH5 : (p_stk_data_pre <> 0)) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stk_chk_self_view sg entry caller p_stk_data_pre selected residual )) (PreH8 : (prio_pre = 255)) (PreH9 : (task_stk_chk_configuration sg )) (PreH10 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio_pre)) (PreH14 : (prio_pre <= 255)) (PreH15 : (prio_pre = 255)) (PreH16 : (p_stk_data_pre <> 0)) (PreH17 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_self_view sg entry caller p_stk_data_pre selected residual ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_self_view sg entry caller p_stk_data_pre selected residual ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre <= 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
.

Definition OSTaskStkChk_partial_solve_wit_8 := OSTaskStkChk_partial_solve_wit_8_pure -> OSTaskStkChk_partial_solve_wit_8_aux.

Definition OSTaskStkChk_partial_solve_wit_9_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH4 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH6 : (0 <= prio)) (PreH7 : (prio <= 63)) (PreH8 : (p_stk_data_pre <> 0)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ”
.

Definition OSTaskStkChk_partial_solve_wit_9_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH4 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH5 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH6 : (0 <= prio)) (PreH7 : (prio <= 63)) (PreH8 : (p_stk_data_pre <> 0)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_9 := OSTaskStkChk_partial_solve_wit_9_pure -> OSTaskStkChk_partial_solve_wit_9_aux.

Definition OSTaskStkChk_partial_solve_wit_10_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_stk_chk_configuration sg )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH8 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (p_stk_data_pre <> 0)) (PreH13 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio))) ”
.

Definition OSTaskStkChk_partial_solve_wit_10_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (task_stk_chk_configuration sg )) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH8 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH9 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH10 : (0 <= prio)) (PreH11 : (prio <= 63)) (PreH12 : (p_stk_data_pre <> 0)) (PreH13 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio))) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_10 := OSTaskStkChk_partial_solve_wit_10_pure -> OSTaskStkChk_partial_solve_wit_10_aux.

Definition OSTaskStkChk_partial_solve_wit_11_pure := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH2 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskStkChk_partial_solve_wit_11_pure_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskStkChk_partial_solve_wit_11_pure_split_goal_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskStkChk_partial_solve_wit_11_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH2 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_11 := OSTaskStkChk_partial_solve_wit_11_pure -> OSTaskStkChk_partial_solve_wit_11_aux.

Definition OSTaskStkChk_partial_solve_wit_12_pure := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH2 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskStkChk_partial_solve_wit_12_pure_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskStkChk_partial_solve_wit_12_pure_split_goal_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskStkChk_partial_solve_wit_12_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 )) (PreH2 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 67 ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_12 := OSTaskStkChk_partial_solve_wit_12_pure -> OSTaskStkChk_partial_solve_wit_12_aux.

Definition OSTaskStkChk_partial_solve_wit_13_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_stk_chk_configuration sg )) (PreH12 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH14 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH15 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (p_stk_data_pre <> 0)) (PreH19 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio))) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ”
.

Definition OSTaskStkChk_partial_solve_wit_13_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio <= 63)) (PreH11 : (task_stk_chk_configuration sg )) (PreH12 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH14 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH15 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 63)) (PreH18 : (p_stk_data_pre <> 0)) (PreH19 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) = (task_stk_chk_table_pointer (sg) (entry) (prio))) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_13 := OSTaskStkChk_partial_solve_wit_13_pure -> OSTaskStkChk_partial_solve_wit_13_aux.

Definition OSTaskStkChk_partial_solve_wit_14_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (task_stk_chk_node_option (node)) 1) = 0)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH8 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH9 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH10 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH11 : (0 <= prio)) (PreH12 : (prio <= 63)) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (task_stk_chk_configuration sg )) (PreH18 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH22 : (0 <= prio)) (PreH23 : (prio <= 63)) (PreH24 : (p_stk_data_pre <> 0)) (PreH25 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ”
.

Definition OSTaskStkChk_partial_solve_wit_14_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (task_stk_chk_node_option (node)) 1) = 0)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH8 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH9 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH10 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH11 : (0 <= prio)) (PreH12 : (prio <= 63)) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (task_stk_chk_configuration sg )) (PreH18 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH22 : (0 <= prio)) (PreH23 : (prio <= 63)) (PreH24 : (p_stk_data_pre <> 0)) (PreH25 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) = 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_14 := OSTaskStkChk_partial_solve_wit_14_pure -> OSTaskStkChk_partial_solve_wit_14_aux.

Definition OSTaskStkChk_partial_solve_wit_15_pure := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH2 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskStkChk_partial_solve_wit_15_pure_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskStkChk_partial_solve_wit_15_pure_split_goal_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH4 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskStkChk_partial_solve_wit_15_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (prio: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 )) (PreH2 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (task_stk_chk_error_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry prio 69 ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_15 := OSTaskStkChk_partial_solve_wit_15_pure -> OSTaskStkChk_partial_solve_wit_15_aux.

Definition OSTaskStkChk_partial_solve_wit_16_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH8 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH9 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH10 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH11 : (0 <= prio)) (PreH12 : (prio <= 63)) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (task_stk_chk_configuration sg )) (PreH18 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH22 : (0 <= prio)) (PreH23 : (prio <= 63)) (PreH24 : (p_stk_data_pre <> 0)) (PreH25 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ”
.

Definition OSTaskStkChk_partial_solve_wit_16_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH5 : (0 <= prio)) (PreH6 : (prio <= 63)) (PreH7 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH8 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH9 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH10 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH11 : (0 <= prio)) (PreH12 : (prio <= 63)) (PreH13 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (0 <= prio)) (PreH16 : (prio <= 63)) (PreH17 : (task_stk_chk_configuration sg )) (PreH18 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH22 : (0 <= prio)) (PreH23 : (prio <= 63)) (PreH24 : (p_stk_data_pre <> 0)) (PreH25 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_16 := OSTaskStkChk_partial_solve_wit_16_pure -> OSTaskStkChk_partial_solve_wit_16_aux.

Definition OSTaskStkChk_partial_solve_wit_17_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH4 : (task_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH10 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH11 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio)) (PreH14 : (prio <= 63)) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH24 : (0 <= prio)) (PreH25 : (prio <= 63)) (PreH26 : (p_stk_data_pre <> 0)) (PreH27 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ”
.

Definition OSTaskStkChk_partial_solve_wit_17_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH4 : (task_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 63)) (PreH9 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH10 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH11 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH12 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH13 : (0 <= prio)) (PreH14 : (prio <= 63)) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH24 : (0 <= prio)) (PreH25 : (prio <= 63)) (PreH26 : (p_stk_data_pre <> 0)) (PreH27 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_17 := OSTaskStkChk_partial_solve_wit_17_pure -> OSTaskStkChk_partial_solve_wit_17_aux.

Definition OSTaskStkChk_partial_solve_wit_18_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (0 <= (task_stk_chk_node_size (node)))) (PreH2 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH5 : (cpu_sr <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : ((task_stk_chk_node_size (node)) >= 0)) (PreH8 : (cpu_sr >= 0)) (PreH9 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH10 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH14 : (task_stk_chk_configuration sg )) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH20 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH21 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_stk_chk_configuration sg )) (PreH30 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH31 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH32 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH33 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH34 : (0 <= prio)) (PreH35 : (prio <= 63)) (PreH36 : (p_stk_data_pre <> 0)) (PreH37 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ”
.

Definition OSTaskStkChk_partial_solve_wit_18_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (0 <= (task_stk_chk_node_size (node)))) (PreH2 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH5 : (cpu_sr <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : ((task_stk_chk_node_size (node)) >= 0)) (PreH8 : (cpu_sr >= 0)) (PreH9 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH10 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH14 : (task_stk_chk_configuration sg )) (PreH15 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH16 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 63)) (PreH19 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH20 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH21 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH22 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH23 : (0 <= prio)) (PreH24 : (prio <= 63)) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH27 : (0 <= prio)) (PreH28 : (prio <= 63)) (PreH29 : (task_stk_chk_configuration sg )) (PreH30 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH31 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH32 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH33 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH34 : (0 <= prio)) (PreH35 : (prio <= 63)) (PreH36 : (p_stk_data_pre <> 0)) (PreH37 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (cpu_sr <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((task_stk_chk_node_size (node)) >= 0) ” 
  &&  “ (cpu_sr >= 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_18 := OSTaskStkChk_partial_solve_wit_18_pure -> OSTaskStkChk_partial_solve_wit_18_aux.

Definition OSTaskStkChk_partial_solve_wit_19_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= (task_stk_chk_node_size (node)))) (PreH5 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH6 : (0 <= (task_stk_chk_node_size (node)))) (PreH7 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH10 : (cpu_sr <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : ((task_stk_chk_node_size (node)) >= 0)) (PreH13 : (cpu_sr >= 0)) (PreH14 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH15 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH16 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH18 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH22 : (0 <= prio)) (PreH23 : (prio <= 63)) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH26 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH27 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH28 : (0 <= prio)) (PreH29 : (prio <= 63)) (PreH30 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH31 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH32 : (0 <= prio)) (PreH33 : (prio <= 63)) (PreH34 : (task_stk_chk_configuration sg )) (PreH35 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH36 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH37 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH38 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH39 : (0 <= prio)) (PreH40 : (prio <= 63)) (PreH41 : (p_stk_data_pre <> 0)) (PreH42 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |->_)
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ”
.

Definition OSTaskStkChk_partial_solve_wit_19_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= (task_stk_chk_node_size (node)))) (PreH5 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH6 : (0 <= (task_stk_chk_node_size (node)))) (PreH7 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH10 : (cpu_sr <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : ((task_stk_chk_node_size (node)) >= 0)) (PreH13 : (cpu_sr >= 0)) (PreH14 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH15 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH16 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH17 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH18 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH19 : (task_stk_chk_configuration sg )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH22 : (0 <= prio)) (PreH23 : (prio <= 63)) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH26 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH27 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH28 : (0 <= prio)) (PreH29 : (prio <= 63)) (PreH30 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH31 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH32 : (0 <= prio)) (PreH33 : (prio <= 63)) (PreH34 : (task_stk_chk_configuration sg )) (PreH35 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH36 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH37 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH38 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH39 : (0 <= prio)) (PreH40 : (prio <= 63)) (PreH41 : (p_stk_data_pre <> 0)) (PreH42 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (cpu_sr <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((task_stk_chk_node_size (node)) >= 0) ” 
  &&  “ (cpu_sr >= 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_19 := OSTaskStkChk_partial_solve_wit_19_pure -> OSTaskStkChk_partial_solve_wit_19_aux.

Definition OSTaskStkChk_partial_solve_wit_20_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= (task_stk_chk_node_size (node)))) (PreH5 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH8 : (0 <= (task_stk_chk_node_size (node)))) (PreH9 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH10 : (0 <= (task_stk_chk_node_size (node)))) (PreH11 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH14 : (cpu_sr <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : ((task_stk_chk_node_size (node)) >= 0)) (PreH17 : (cpu_sr >= 0)) (PreH18 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH19 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH22 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH23 : (task_stk_chk_configuration sg )) (PreH24 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH25 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH26 : (0 <= prio)) (PreH27 : (prio <= 63)) (PreH28 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH29 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH30 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH31 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH32 : (0 <= prio)) (PreH33 : (prio <= 63)) (PreH34 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH35 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH36 : (0 <= prio)) (PreH37 : (prio <= 63)) (PreH38 : (task_stk_chk_configuration sg )) (PreH39 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH40 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH41 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH42 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH43 : (0 <= prio)) (PreH44 : (prio <= 63)) (PreH45 : (p_stk_data_pre <> 0)) (PreH46 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_bottom (node)) = (task_stk_chk_node_bottom (node))) ”
.

Definition OSTaskStkChk_partial_solve_wit_20_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= (task_stk_chk_node_size (node)))) (PreH5 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH6 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH7 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH8 : (0 <= (task_stk_chk_node_size (node)))) (PreH9 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH10 : (0 <= (task_stk_chk_node_size (node)))) (PreH11 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH14 : (cpu_sr <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : ((task_stk_chk_node_size (node)) >= 0)) (PreH17 : (cpu_sr >= 0)) (PreH18 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH19 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH20 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH21 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH22 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH23 : (task_stk_chk_configuration sg )) (PreH24 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH25 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH26 : (0 <= prio)) (PreH27 : (prio <= 63)) (PreH28 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH29 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH30 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH31 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH32 : (0 <= prio)) (PreH33 : (prio <= 63)) (PreH34 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH35 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH36 : (0 <= prio)) (PreH37 : (prio <= 63)) (PreH38 : (task_stk_chk_configuration sg )) (PreH39 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH40 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH41 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH42 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH43 : (0 <= prio)) (PreH44 : (prio <= 63)) (PreH45 : (p_stk_data_pre <> 0)) (PreH46 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_bottom (node)) = (task_stk_chk_node_bottom (node))) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (cpu_sr <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((task_stk_chk_node_size (node)) >= 0) ” 
  &&  “ (cpu_sr >= 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((&(((task_stk_chk_table_pointer (sg) (entry) (prio)))  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_20 := OSTaskStkChk_partial_solve_wit_20_pure -> OSTaskStkChk_partial_solve_wit_20_aux.

Definition OSTaskStkChk_partial_solve_wit_21_pure := 
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= (task_stk_chk_node_size (node)))) (PreH5 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH6 : ((task_stk_chk_node_bottom (node)) = (task_stk_chk_node_bottom (node)))) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH9 : (0 <= (task_stk_chk_node_size (node)))) (PreH10 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= (task_stk_chk_node_size (node)))) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH19 : (cpu_sr <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : ((task_stk_chk_node_size (node)) >= 0)) (PreH22 : (cpu_sr >= 0)) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH27 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH28 : (task_stk_chk_configuration sg )) (PreH29 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH30 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH31 : (0 <= prio)) (PreH32 : (prio <= 63)) (PreH33 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH34 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH35 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH36 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH37 : (0 <= prio)) (PreH38 : (prio <= 63)) (PreH39 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH40 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH41 : (0 <= prio)) (PreH42 : (prio <= 63)) (PreH43 : (task_stk_chk_configuration sg )) (PreH44 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH45 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH46 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH47 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH48 : (0 <= prio)) (PreH49 : (prio <= 63)) (PreH50 : (p_stk_data_pre <> 0)) (PreH51 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ”
) \/
(
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : (0 <= (task_stk_chk_node_size (node)))) (PreH4 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH7 : (0 <= (task_stk_chk_node_size (node)))) (PreH8 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH9 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH10 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH11 : (0 <= (task_stk_chk_node_size (node)))) (PreH12 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (cpu_sr <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : ((task_stk_chk_node_size (node)) >= 0)) (PreH20 : (cpu_sr >= 0)) (PreH21 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH22 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH26 : (task_stk_chk_configuration sg )) (PreH27 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH28 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH29 : (0 <= prio)) (PreH30 : (prio <= 63)) (PreH31 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH32 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH33 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH34 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH35 : (0 <= prio)) (PreH36 : (prio <= 63)) (PreH37 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH38 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH39 : (0 <= prio)) (PreH40 : (prio <= 63)) (PreH41 : (task_stk_chk_configuration sg )) (PreH42 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH43 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH44 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH45 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH46 : (0 <= prio)) (PreH47 : (prio <= 63)) (PreH48 : (p_stk_data_pre <> 0)) (PreH49 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ”
).

Definition OSTaskStkChk_partial_solve_wit_21_pure_split_goal_1 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : (0 <= (task_stk_chk_node_size (node)))) (PreH4 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH7 : (0 <= (task_stk_chk_node_size (node)))) (PreH8 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH9 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH10 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH11 : (0 <= (task_stk_chk_node_size (node)))) (PreH12 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (cpu_sr <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : ((task_stk_chk_node_size (node)) >= 0)) (PreH20 : (cpu_sr >= 0)) (PreH21 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH22 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH26 : (task_stk_chk_configuration sg )) (PreH27 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH28 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH29 : (0 <= prio)) (PreH30 : (prio <= 63)) (PreH31 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH32 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH33 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH34 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH35 : (0 <= prio)) (PreH36 : (prio <= 63)) (PreH37 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH38 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH39 : (0 <= prio)) (PreH40 : (prio <= 63)) (PreH41 : (task_stk_chk_configuration sg )) (PreH42 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH43 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH44 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH45 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH46 : (0 <= prio)) (PreH47 : (prio <= 63)) (PreH48 : (p_stk_data_pre <> 0)) (PreH49 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (valid_os_cpu_sr cpu_sr ) ”
.

Definition OSTaskStkChk_partial_solve_wit_21_pure_split_goal_2 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : (0 <= (task_stk_chk_node_size (node)))) (PreH4 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH5 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH6 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH7 : (0 <= (task_stk_chk_node_size (node)))) (PreH8 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH9 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH10 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH11 : (0 <= (task_stk_chk_node_size (node)))) (PreH12 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (cpu_sr <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : ((task_stk_chk_node_size (node)) >= 0)) (PreH20 : (cpu_sr >= 0)) (PreH21 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH22 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH26 : (task_stk_chk_configuration sg )) (PreH27 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH28 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH29 : (0 <= prio)) (PreH30 : (prio <= 63)) (PreH31 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH32 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH33 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH34 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH35 : (0 <= prio)) (PreH36 : (prio <= 63)) (PreH37 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH38 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH39 : (0 <= prio)) (PreH40 : (prio <= 63)) (PreH41 : (task_stk_chk_configuration sg )) (PreH42 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH43 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH44 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH45 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH46 : (0 <= prio)) (PreH47 : (prio <= 63)) (PreH48 : (p_stk_data_pre <> 0)) (PreH49 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_node_size (node)))
  **  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (UCOS2_inv sg entry )
  **  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
|--
  “ (UCOS2_state_inv sg entry ) ”
.

Definition OSTaskStkChk_partial_solve_wit_21_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (slot: Z) (node: TaskAbstractState) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH3 : ((task_stk_chk_node_size (node)) = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= (task_stk_chk_node_size (node)))) (PreH5 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH6 : ((task_stk_chk_node_bottom (node)) = (task_stk_chk_node_bottom (node)))) (PreH7 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH8 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH9 : (0 <= (task_stk_chk_node_size (node)))) (PreH10 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH11 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH12 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH13 : (0 <= (task_stk_chk_node_size (node)))) (PreH14 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH15 : (0 <= (task_stk_chk_node_size (node)))) (PreH16 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH19 : (cpu_sr <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : ((task_stk_chk_node_size (node)) >= 0)) (PreH22 : (cpu_sr >= 0)) (PreH23 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH24 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH25 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH26 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH27 : ((Z.land (task_stk_chk_node_option (node)) 1) <> 0)) (PreH28 : (task_stk_chk_configuration sg )) (PreH29 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH30 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH31 : (0 <= prio)) (PreH32 : (prio <= 63)) (PreH33 : (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node )) (PreH34 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1)) (PreH35 : ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0)) (PreH36 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH37 : (0 <= prio)) (PreH38 : (prio <= 63)) (PreH39 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH40 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH41 : (0 <= prio)) (PreH42 : (prio <= 63)) (PreH43 : (task_stk_chk_configuration sg )) (PreH44 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH45 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre )) (PreH46 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH47 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio )) (PreH48 : (0 <= prio)) (PreH49 : (prio <= 63)) (PreH50 : (p_stk_data_pre <> 0)) (PreH51 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (UCOS2_inv sg entry )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (valid_os_cpu_sr cpu_sr ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= (task_stk_chk_node_size (node))) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((task_stk_chk_node_size (node)) <= UINT_MAX) ” 
  &&  “ (cpu_sr <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((task_stk_chk_node_size (node)) >= 0) ” 
  &&  “ (cpu_sr >= 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((Z.land (task_stk_chk_node_option (node)) 1) <> 0) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio (task_stk_chk_table_pointer (sg) (entry) (prio)) slot node ) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 1) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (entry) (prio)) <> 0) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data_pre ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data_pre prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (p_stk_data_pre <> 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
.

Definition OSTaskStkChk_partial_solve_wit_21 := OSTaskStkChk_partial_solve_wit_21_pure -> OSTaskStkChk_partial_solve_wit_21_aux.

Definition OSTaskStkChk_partial_solve_wit_22_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (prio: Z) (cpu_sr: Z) (ptcb: Z) (size: Z) (pchk: Z) (nfree: Z) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (snapshot = (task_stk_chk_node_snapshot (slot) (node)))) (PreH3 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH4 : (size = (task_stk_chk_size (snapshot)))) (PreH5 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH6 : (0 <= size)) (PreH7 : (size <= UINT_MAX)) (PreH8 : (nfree = 0)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "size" ) )) # UInt  |-> size)
  **  ((( &( "pchk" ) )) # Ptr  |-> pchk)
  **  ((( &( "nfree" ) )) # UInt  |-> nfree)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ ((task_stk_chk_bottom (snapshot)) = (task_stk_chk_bottom (snapshot))) ” 
  &&  “ ((task_stk_chk_size (snapshot)) = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 = 0) ”
.

Definition OSTaskStkChk_partial_solve_wit_22_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (prio: Z) (cpu_sr: Z) (ptcb: Z) (size: Z) (pchk: Z) (nfree: Z) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (snapshot = (task_stk_chk_node_snapshot (slot) (node)))) (PreH3 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH4 : (size = (task_stk_chk_size (snapshot)))) (PreH5 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH6 : (0 <= size)) (PreH7 : (size <= UINT_MAX)) (PreH8 : (nfree = 0)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "size" ) )) # UInt  |-> size)
  **  ((( &( "pchk" ) )) # Ptr  |-> pchk)
  **  ((( &( "nfree" ) )) # UInt  |-> nfree)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ ((task_stk_chk_bottom (snapshot)) = (task_stk_chk_bottom (snapshot))) ” 
  &&  “ ((task_stk_chk_size (snapshot)) = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (snapshot = (task_stk_chk_node_snapshot (slot) (node))) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (pchk = (task_stk_chk_bottom (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (nfree = 0) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((( &( "pchk" ) )) # Ptr  |-> (task_stk_chk_bottom (snapshot)))
  **  ((( &( "size" ) )) # UInt  |-> (task_stk_chk_size (snapshot)))
  **  ((( &( "nfree" ) )) # UInt  |-> 0)
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSTaskStkChk_partial_solve_wit_22 := OSTaskStkChk_partial_solve_wit_22_pure -> OSTaskStkChk_partial_solve_wit_22_aux.

Definition OSTaskStkChk_partial_solve_wit_23 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (size_2: Z) (pchk_2: Z) (index: Z) (cpu_sr_2: Z) (prio_2: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual )) (PreH2 : (0 <= index)) (PreH3 : (index <= (task_stk_chk_count (count)))) (PreH4 : (pchk_2 = (task_stk_chk_cursor (snapshot) (index)))) (PreH5 : (size_2 = (task_stk_chk_size (snapshot)))) (PreH6 : (0 <= size_2)) (PreH7 : (size_2 <= UINT_MAX)) (PreH8 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) (PreH9 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH10 : (pchk = (task_stk_chk_cursor (snapshot) (0)))) (PreH11 : (nfree = 0)) (PreH12 : (size = (task_stk_chk_size (snapshot)))) (PreH13 : (0 <= size)) (PreH14 : (size <= UINT_MAX)) (PreH15 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (index))) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (task_stk_chk_scan_read_frame region words index residual )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr_2 entry after prio_2 snapshot region words count stop residual ) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= (task_stk_chk_count (count))) ” 
  &&  “ (pchk_2 = (task_stk_chk_cursor (snapshot) (index))) ” 
  &&  “ (size_2 = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size_2) ” 
  &&  “ (size_2 <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (pchk = (task_stk_chk_cursor (snapshot) (0))) ” 
  &&  “ (nfree = 0) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((pchk_2) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (interrupt_platform_running platform invocation origin mask )
  **  (task_stk_chk_scan_read_frame region words index residual )
.

Definition OSTaskStkChk_partial_solve_wit_24_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (previous: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (0 <= previous)) (PreH3 : (previous < (task_stk_chk_count (count)))) (PreH4 : (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH5 : (nfree = (previous + 1 ))) (PreH6 : (size = (task_stk_chk_size (snapshot)))) (PreH7 : (0 <= size)) (PreH8 : (size <= UINT_MAX)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pchk" ) )) # Ptr  |-> pchk)
  **  ((( &( "nfree" ) )) # UInt  |-> nfree)
  **  ((( &( "size" ) )) # UInt  |-> size)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= previous) ” 
  &&  “ (previous < (task_stk_chk_count (count))) ” 
  &&  “ (((task_stk_chk_cursor (snapshot) (previous)) + 4 ) = ((task_stk_chk_cursor (snapshot) (previous)) + 4 )) ” 
  &&  “ ((previous + 1 ) = (previous + 1 )) ”
.

Definition OSTaskStkChk_partial_solve_wit_24_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (pchk: Z) (nfree: Z) (size: Z) (previous: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (0 <= previous)) (PreH3 : (previous < (task_stk_chk_count (count)))) (PreH4 : (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH5 : (nfree = (previous + 1 ))) (PreH6 : (size = (task_stk_chk_size (snapshot)))) (PreH7 : (0 <= size)) (PreH8 : (size <= UINT_MAX)) (PreH9 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "pchk" ) )) # Ptr  |-> pchk)
  **  ((( &( "nfree" ) )) # UInt  |-> nfree)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= previous) ” 
  &&  “ (previous < (task_stk_chk_count (count))) ” 
  &&  “ (((task_stk_chk_cursor (snapshot) (previous)) + 4 ) = ((task_stk_chk_cursor (snapshot) (previous)) + 4 )) ” 
  &&  “ ((previous + 1 ) = (previous + 1 )) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= previous) ” 
  &&  “ (previous < (task_stk_chk_count (count))) ” 
  &&  “ (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 )) ” 
  &&  “ (nfree = (previous + 1 )) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((( &( "pchk" ) )) # Ptr  |-> ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))
  **  ((( &( "nfree" ) )) # UInt  |-> (previous + 1 ))
  **  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSTaskStkChk_partial_solve_wit_24 := OSTaskStkChk_partial_solve_wit_24_pure -> OSTaskStkChk_partial_solve_wit_24_aux.

Definition OSTaskStkChk_partial_solve_wit_25_pure := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (nfree: Z) (pchk: Z) (size: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (nfree = (task_stk_chk_count (count)))) (PreH3 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) (PreH4 : (size = (task_stk_chk_size (snapshot)))) (PreH5 : (0 <= size)) (PreH6 : (size <= UINT_MAX)) (PreH7 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "p_stk_data" ) )) # Ptr  |-> p_stk_data_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "nfree" ) )) # UInt  |-> nfree)
  **  ((( &( "pchk" ) )) # Ptr  |-> pchk)
  **  ((( &( "size" ) )) # UInt  |-> size)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ ((task_stk_chk_count (count)) = (task_stk_chk_count (count))) ” 
  &&  “ (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ) = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ”
.

Definition OSTaskStkChk_partial_solve_wit_25_aux := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (nfree: Z) (pchk: Z) (size: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (nfree = (task_stk_chk_count (count)))) (PreH3 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) (PreH4 : (size = (task_stk_chk_size (snapshot)))) (PreH5 : (0 <= size)) (PreH6 : (size <= UINT_MAX)) (PreH7 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  ((( &( "nfree" ) )) # UInt  |-> nfree)
  **  ((( &( "pchk" ) )) # Ptr  |-> pchk)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ ((task_stk_chk_count (count)) = (task_stk_chk_count (count))) ” 
  &&  “ (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ) = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (nfree = (task_stk_chk_count (count))) ” 
  &&  “ (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  ((( &( "nfree" ) )) # UInt  |-> (task_stk_chk_count (count)))
  **  ((( &( "pchk" ) )) # Ptr  |-> ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))
  **  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSTaskStkChk_partial_solve_wit_25 := OSTaskStkChk_partial_solve_wit_25_pure -> OSTaskStkChk_partial_solve_wit_25_aux.

Definition OSTaskStkChk_partial_solve_wit_26 := 
forall (p_stk_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@option TaskStackCheckData) -> (UCOS2_Verify_State -> Prop)))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (nfree: Z) (pchk: Z) (size: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : ((task_stk_chk_count (count)) = (task_stk_chk_count (count)))) (PreH3 : (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ) = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) (PreH4 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual )) (PreH5 : (nfree = (task_stk_chk_count (count)))) (PreH6 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) (PreH7 : (size = (task_stk_chk_size (snapshot)))) (PreH8 : (0 <= size)) (PreH9 : (size <= UINT_MAX)) (PreH10 : (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X )) ,
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data_pre cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (nfree = (task_stk_chk_count (count))) ” 
  &&  “ (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (task_stk_chk_safe critical sg invocation before caller prio_pre p_stk_data_pre X ) ”
  &&  (task_stack_check_data_rep p_stk_data_pre task_stack_check_zero_data )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSTaskStkChk_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (p_stk_data: Z) (prio: Z) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio p_stk_data )) ,
  (task_stk_chk_output_pre sg prio p_stk_data )
|--
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio p_stk_data ) ”
  &&  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |->_)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |->_)
) \/
(
forall (sg: StableGlobVars) (p_stk_data: Z) (prio: Z) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_valid_arguments prio p_stk_data )) ,
  (task_stk_chk_output_pre sg prio p_stk_data )
|--
  EX (x_2: Z)  (x: Z) ,
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_valid_arguments prio p_stk_data ) ”
  &&  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> x_2)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> x)
).

Definition OSTaskStkChk_which_implies_wit_2 := 
(
forall (p_stk_data: Z) ,
  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
|--
  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
) \/
(
forall (p_stk_data: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) ,
  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
|--
  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
).

Definition OSTaskStkChk_which_implies_wit_2_split_goal_spatial := 
forall (p_stk_data: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) ,
  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
|--
  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
.

Definition OSTaskStkChk_which_implies_wit_3 := 
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (p_stk_data: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data )) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_stk_chk_configuration sg )) (PreH4 : (prio_pre = 255)) (PreH5 : (p_stk_data <> 0)) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  EX (selected: Z)  (residual: Assertion) ,
  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data <> 0) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_self_view sg entry caller p_stk_data selected residual ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
) \/
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (p_stk_data: Z) (cpu_sr: Z) (PreH1 : (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data )) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_stk_chk_configuration sg )) (PreH4 : (prio_pre = 255)) (PreH5 : (p_stk_data <> 0)) (PreH6 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  EX (selected: Z)  (residual: Assertion) ,
  “ (task_stk_chk_admission critical sg invocation before caller prio_pre p_stk_data ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (p_stk_data <> 0) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_self_view sg entry caller p_stk_data selected residual ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
).

Definition OSTaskStkChk_which_implies_wit_4 := 
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (cpu_sr: Z) (p_stk_data: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_self_view sg entry caller p_stk_data selected residual )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (prio_pre = 255)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data selected ) ” 
  &&  “ (0 <= selected) ” 
  &&  “ (selected <= 63) ”
  &&  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
) \/
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (cpu_sr: Z) (p_stk_data: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_self_view sg entry caller p_stk_data selected residual )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (prio_pre = 255)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
|--
  “ (selected <= 63) ” 
  &&  “ (0 <= selected) ” 
  &&  “ (task_stk_chk_selected sg entry caller 255 p_stk_data selected ) ”
  &&  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
).

Definition OSTaskStkChk_which_implies_wit_4_split_goal_1 := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (cpu_sr: Z) (p_stk_data: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_self_view sg entry caller p_stk_data selected residual )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (prio_pre = 255)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
|--
  “ (selected <= 63) ”
.

Definition OSTaskStkChk_which_implies_wit_4_split_goal_2 := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (cpu_sr: Z) (p_stk_data: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_self_view sg entry caller p_stk_data selected residual )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (prio_pre = 255)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
|--
  “ (0 <= selected) ”
.

Definition OSTaskStkChk_which_implies_wit_4_split_goal_3 := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (cpu_sr: Z) (p_stk_data: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_self_view sg entry caller p_stk_data selected residual )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (prio_pre = 255)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
|--
  “ (task_stk_chk_selected sg entry caller 255 p_stk_data selected ) ”
.

Definition OSTaskStkChk_which_implies_wit_4_split_goal_spatial := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (selected: Z) (residual: Assertion) (cpu_sr: Z) (p_stk_data: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_self_view sg entry caller p_stk_data selected residual )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (prio_pre = 255)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_stk_chk_current_pointer (sg) (entry)))
  **  ((&(((task_stk_chk_current_pointer (sg) (entry)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> selected)
  **  (task_stk_chk_residual residual )
|--
  (UCOS2_inv sg entry )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
.

Definition OSTaskStkChk_which_implies_wit_5 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) ,
  (UCOS2_inv sg entry )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) ,
  (UCOS2_inv sg entry )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
).

Definition OSTaskStkChk_which_implies_wit_5_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) ,
  (UCOS2_inv sg entry )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
.

Definition OSTaskStkChk_which_implies_wit_6 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (entry) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (ptcb = (task_stk_chk_table_pointer (sg) (entry) (prio))) ”
  &&  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (entry) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
|--
  (UCOS2_inv sg entry )
).

Definition OSTaskStkChk_which_implies_wit_6_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (ptcb: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio <= 63)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (entry) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (entry) (prio)))
  **  (task_stk_chk_table_frame sg entry prio )
|--
  (UCOS2_inv sg entry )
.

Definition OSTaskStkChk_which_implies_wit_7 := 
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (p_stk_data: Z) (ptcb: Z) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data prio )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : (ptcb = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) ,
  (UCOS2_inv sg entry )
|--
  EX (slot: Z)  (node: TaskAbstractState) ,
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
) \/
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (p_stk_data: Z) (ptcb: Z) (PreH1 : (task_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH3 : (task_stk_chk_selected sg entry caller prio_pre p_stk_data prio )) (PreH4 : (0 <= prio)) (PreH5 : (prio <= 63)) (PreH6 : (ptcb = (task_stk_chk_table_pointer (sg) (entry) (prio)))) (PreH7 : (ptcb <> 0)) (PreH8 : (ptcb <> 1)) ,
  (UCOS2_inv sg entry )
|--
  EX (slot: Z)  (node: TaskAbstractState) ,
  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_selected sg entry caller prio_pre p_stk_data prio ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
).

Definition OSTaskStkChk_which_implies_wit_8 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ”
  &&  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
|--
  (UCOS2_inv sg entry )
).

Definition OSTaskStkChk_which_implies_wit_8_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
|--
  (UCOS2_inv sg entry )
.

Definition OSTaskStkChk_which_implies_wit_9 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ”
  &&  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
|--
  (UCOS2_inv sg entry )
).

Definition OSTaskStkChk_which_implies_wit_9_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> (task_stk_chk_node_option (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBOpt )
|--
  (UCOS2_inv sg entry )
.

Definition OSTaskStkChk_which_implies_wit_10 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  (UCOS2_inv sg entry )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  (UCOS2_inv sg entry )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
).

Definition OSTaskStkChk_which_implies_wit_10_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) ,
  (UCOS2_inv sg entry )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
.

Definition OSTaskStkChk_which_implies_wit_11 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ” 
  &&  “ (size = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ”
  &&  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (PreH1 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_node_size (node)) >= 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH5 : (size = (task_stk_chk_node_size (node)))) (PreH6 : (0 <= size)) (PreH7 : (size <= UINT_MAX)) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
|--
  (UCOS2_inv sg entry )
).

Definition OSTaskStkChk_which_implies_wit_11_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (PreH1 : ((task_stk_chk_node_size (node)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_node_size (node)) >= 0)) (PreH3 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH4 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH5 : (size = (task_stk_chk_node_size (node)))) (PreH6 : (0 <= size)) (PreH7 : (size <= UINT_MAX)) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> (task_stk_chk_node_size (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkSize )
|--
  (UCOS2_inv sg entry )
.

Definition OSTaskStkChk_which_implies_wit_12 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) ,
  (UCOS2_inv sg entry )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ” 
  &&  “ (size = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) ,
  (UCOS2_inv sg entry )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
).

Definition OSTaskStkChk_which_implies_wit_12_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) ,
  (UCOS2_inv sg entry )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
.

Definition OSTaskStkChk_which_implies_wit_13 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (pchk: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) (PreH6 : (pchk = (task_stk_chk_node_bottom (node)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
|--
  “ (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry ) ” 
  &&  “ (task_stk_chk_node sg entry prio ptcb slot node ) ” 
  &&  “ (size = (task_stk_chk_node_size (node))) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= UINT_MAX) ” 
  &&  “ (pchk = (task_stk_chk_node_bottom (node))) ”
  &&  (UCOS2_inv sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (pchk: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) (PreH6 : (pchk = (task_stk_chk_node_bottom (node)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
|--
  (UCOS2_inv sg entry )
).

Definition OSTaskStkChk_which_implies_wit_13_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (slot: Z) (node: TaskAbstractState) (cpu_sr: Z) (ptcb: Z) (prio: Z) (size: Z) (pchk: Z) (PreH1 : (task_stk_chk_acquire_facts critical sg invocation mask cpu_sr before entry )) (PreH2 : (task_stk_chk_node sg entry prio ptcb slot node )) (PreH3 : (size = (task_stk_chk_node_size (node)))) (PreH4 : (0 <= size)) (PreH5 : (size <= UINT_MAX)) (PreH6 : (pchk = (task_stk_chk_node_bottom (node)))) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> (task_stk_chk_node_bottom (node)))
  **  (task_stk_chk_field_frame sg entry slot node TCBStkBottom )
|--
  (UCOS2_inv sg entry )
.

Definition OSTaskStkChk_which_implies_wit_14 := 
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (size: Z) (nfree: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH3 : (size = (task_stk_chk_size (snapshot)))) (PreH4 : (nfree = 0)) ,
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (pchk = (task_stk_chk_cursor (snapshot) (0))) ” 
  &&  “ (size = (task_stk_chk_size (snapshot))) ” 
  &&  “ (nfree = 0) ”
  &&  (((task_stk_chk_cursor (snapshot) (0))) # UInt  |-> (task_stk_chk_word (count) (stop) (0)))
  **  (task_stk_chk_scan_read_frame region words 0 residual )
) \/
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (size: Z) (nfree: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH3 : (size = (task_stk_chk_size (snapshot)))) (PreH4 : (nfree = 0)) ,
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  “ (pchk = (task_stk_chk_cursor (snapshot) (0))) ”
  &&  (((task_stk_chk_cursor (snapshot) (0))) # UInt  |-> (task_stk_chk_word (count) (stop) (0)))
  **  (task_stk_chk_scan_read_frame region words 0 residual )
).

Definition OSTaskStkChk_which_implies_wit_14_split_goal_1 := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (size: Z) (nfree: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH3 : (size = (task_stk_chk_size (snapshot)))) (PreH4 : (nfree = 0)) ,
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  “ (pchk = (task_stk_chk_cursor (snapshot) (0))) ”
.

Definition OSTaskStkChk_which_implies_wit_14_split_goal_spatial := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (size: Z) (nfree: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (pchk = (task_stk_chk_bottom (snapshot)))) (PreH3 : (size = (task_stk_chk_size (snapshot)))) (PreH4 : (nfree = 0)) ,
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  (((task_stk_chk_cursor (snapshot) (0))) # UInt  |-> (task_stk_chk_word (count) (stop) (0)))
  **  (task_stk_chk_scan_read_frame region words 0 residual )
.

Definition OSTaskStkChk_which_implies_wit_15 := 
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (previous: Z) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (nfree: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (0 <= previous)) (PreH3 : (previous < (task_stk_chk_count (count)))) (PreH4 : (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH5 : (nfree = (previous + 1 ))) ,
  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
|--
  EX (index: Z) ,
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= (task_stk_chk_count (count))) ” 
  &&  “ (pchk = (task_stk_chk_cursor (snapshot) (index))) ” 
  &&  “ (nfree = index) ”
  &&  (((task_stk_chk_cursor (snapshot) (index))) # UInt  |-> (task_stk_chk_word (count) (stop) (index)))
  **  (task_stk_chk_scan_read_frame region words index residual )
) \/
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (previous: Z) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (nfree: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (previous)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (previous)) >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (0 <= previous)) (PreH5 : (previous < (task_stk_chk_count (count)))) (PreH6 : (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH7 : (nfree = (previous + 1 ))) ,
  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
|--
  “ (pchk = (task_stk_chk_cursor (snapshot) ((previous + 1 )))) ”
  &&  (((task_stk_chk_cursor (snapshot) (nfree))) # UInt  |-> (task_stk_chk_word (count) (stop) (nfree)))
  **  (task_stk_chk_scan_read_frame region words nfree residual )
).

Definition OSTaskStkChk_which_implies_wit_15_split_goal_1 := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (previous: Z) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (nfree: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (previous)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (previous)) >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (0 <= previous)) (PreH5 : (previous < (task_stk_chk_count (count)))) (PreH6 : (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH7 : (nfree = (previous + 1 ))) ,
  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
|--
  “ (pchk = (task_stk_chk_cursor (snapshot) ((previous + 1 )))) ”
.

Definition OSTaskStkChk_which_implies_wit_15_split_goal_spatial := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (previous: Z) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (pchk: Z) (nfree: Z) (PreH1 : ((task_stk_chk_word (count) (stop) (previous)) <= UINT_MAX)) (PreH2 : ((task_stk_chk_word (count) (stop) (previous)) >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (0 <= previous)) (PreH5 : (previous < (task_stk_chk_count (count)))) (PreH6 : (pchk = ((task_stk_chk_cursor (snapshot) (previous)) + 4 ))) (PreH7 : (nfree = (previous + 1 ))) ,
  (((task_stk_chk_cursor (snapshot) (previous))) # UInt  |-> (task_stk_chk_word (count) (stop) (previous)))
  **  (task_stk_chk_scan_read_frame region words previous residual )
|--
  (((task_stk_chk_cursor (snapshot) (nfree))) # UInt  |-> (task_stk_chk_word (count) (stop) (nfree)))
  **  (task_stk_chk_scan_read_frame region words nfree residual )
.

Definition OSTaskStkChk_which_implies_wit_16 := 
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (nfree: Z) (pchk: Z) (PreH1 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH2 : (nfree = (task_stk_chk_count (count)))) (PreH3 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) ,
  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
|--
  “ (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual ) ” 
  &&  “ (nfree = (task_stk_chk_count (count))) ” 
  &&  “ (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 )) ”
  &&  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
) \/
(
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (nfree: Z) (pchk: Z) (PreH1 : (stop <= UINT_MAX)) (PreH2 : (stop >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (nfree = (task_stk_chk_count (count)))) (PreH5 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) ,
  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
|--
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
).

Definition OSTaskStkChk_which_implies_wit_16_split_goal_spatial := 
forall (prio_pre: Z) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (after: UCOS2_Verify_State) (snapshot: TaskStackCheckSnapshot) (region: TaskStackRegion) (words: TaskStkChkWords) (count: nat) (stop: Z) (residual: Assertion) (prio: Z) (cpu_sr: Z) (p_stk_data: Z) (nfree: Z) (pchk: Z) (PreH1 : (stop <= UINT_MAX)) (PreH2 : (stop >= 0)) (PreH3 : (task_stk_chk_scan_facts critical sg invocation mask before caller prio_pre p_stk_data cpu_sr entry after prio snapshot region words count stop residual )) (PreH4 : (nfree = (task_stk_chk_count (count)))) (PreH5 : (pchk = ((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count)))) + 4 ))) ,
  (((task_stk_chk_cursor (snapshot) ((task_stk_chk_count (count))))) # UInt  |-> stop)
  **  (task_stk_chk_scan_read_frame region words (task_stk_chk_count (count)) residual )
|--
  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
.

Definition OSTaskStkChk_which_implies_wit_17 := 
(
forall (p_stk_data: Z) ,
  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
) \/
(
forall (p_stk_data: Z) ,
  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
).

Definition OSTaskStkChk_which_implies_wit_17_split_goal_spatial := 
forall (p_stk_data: Z) ,
  (task_stack_check_data_rep p_stk_data task_stack_check_zero_data )
|--
  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSFree")) # UInt  |-> 0)
  **  ((&((p_stk_data)  # "os_stk_data" ->ₛ "OSUsed")) # UInt  |-> 0)
.

Module Type VC_Correct.


Axiom proof_of_OSTaskStkChk_safety_wit_1 : OSTaskStkChk_safety_wit_1.
Axiom proof_of_OSTaskStkChk_safety_wit_2 : OSTaskStkChk_safety_wit_2.
Axiom proof_of_OSTaskStkChk_safety_wit_3 : OSTaskStkChk_safety_wit_3.
Axiom proof_of_OSTaskStkChk_safety_wit_4 : OSTaskStkChk_safety_wit_4.
Axiom proof_of_OSTaskStkChk_safety_wit_5 : OSTaskStkChk_safety_wit_5.
Axiom proof_of_OSTaskStkChk_safety_wit_6 : OSTaskStkChk_safety_wit_6.
Axiom proof_of_OSTaskStkChk_safety_wit_7 : OSTaskStkChk_safety_wit_7.
Axiom proof_of_OSTaskStkChk_safety_wit_8 : OSTaskStkChk_safety_wit_8.
Axiom proof_of_OSTaskStkChk_safety_wit_9 : OSTaskStkChk_safety_wit_9.
Axiom proof_of_OSTaskStkChk_safety_wit_10 : OSTaskStkChk_safety_wit_10.
Axiom proof_of_OSTaskStkChk_safety_wit_11 : OSTaskStkChk_safety_wit_11.
Axiom proof_of_OSTaskStkChk_safety_wit_12 : OSTaskStkChk_safety_wit_12.
Axiom proof_of_OSTaskStkChk_safety_wit_13 : OSTaskStkChk_safety_wit_13.
Axiom proof_of_OSTaskStkChk_entail_wit_1_1 : OSTaskStkChk_entail_wit_1_1.
Axiom proof_of_OSTaskStkChk_entail_wit_1_2 : OSTaskStkChk_entail_wit_1_2.
Axiom proof_of_OSTaskStkChk_entail_wit_2_1 : OSTaskStkChk_entail_wit_2_1.
Axiom proof_of_OSTaskStkChk_entail_wit_2_2 : OSTaskStkChk_entail_wit_2_2.
Axiom proof_of_OSTaskStkChk_entail_wit_3 : OSTaskStkChk_entail_wit_3.
Axiom proof_of_OSTaskStkChk_entail_wit_4 : OSTaskStkChk_entail_wit_4.
Axiom proof_of_OSTaskStkChk_entail_wit_5 : OSTaskStkChk_entail_wit_5.
Axiom proof_of_OSTaskStkChk_entail_wit_6 : OSTaskStkChk_entail_wit_6.
Axiom proof_of_OSTaskStkChk_entail_wit_7 : OSTaskStkChk_entail_wit_7.
Axiom proof_of_OSTaskStkChk_entail_wit_8 : OSTaskStkChk_entail_wit_8.
Axiom proof_of_OSTaskStkChk_entail_wit_9 : OSTaskStkChk_entail_wit_9.
Axiom proof_of_OSTaskStkChk_entail_wit_10 : OSTaskStkChk_entail_wit_10.
Axiom proof_of_OSTaskStkChk_entail_wit_11 : OSTaskStkChk_entail_wit_11.
Axiom proof_of_OSTaskStkChk_entail_wit_12 : OSTaskStkChk_entail_wit_12.
Axiom proof_of_OSTaskStkChk_return_wit_1 : OSTaskStkChk_return_wit_1.
Axiom proof_of_OSTaskStkChk_return_wit_2 : OSTaskStkChk_return_wit_2.
Axiom proof_of_OSTaskStkChk_return_wit_3 : OSTaskStkChk_return_wit_3.
Axiom proof_of_OSTaskStkChk_return_wit_4 : OSTaskStkChk_return_wit_4.
Axiom proof_of_OSTaskStkChk_return_wit_5 : OSTaskStkChk_return_wit_5.
Axiom proof_of_OSTaskStkChk_return_wit_6 : OSTaskStkChk_return_wit_6.
Axiom proof_of_OSTaskStkChk_return_wit_7 : OSTaskStkChk_return_wit_7.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_1_pure : OSTaskStkChk_partial_solve_wit_1_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_1 : OSTaskStkChk_partial_solve_wit_1.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_2_pure : OSTaskStkChk_partial_solve_wit_2_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_2 : OSTaskStkChk_partial_solve_wit_2.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_3 : OSTaskStkChk_partial_solve_wit_3.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_4 : OSTaskStkChk_partial_solve_wit_4.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_5_pure : OSTaskStkChk_partial_solve_wit_5_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_5 : OSTaskStkChk_partial_solve_wit_5.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_6_pure : OSTaskStkChk_partial_solve_wit_6_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_6 : OSTaskStkChk_partial_solve_wit_6.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_7_pure : OSTaskStkChk_partial_solve_wit_7_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_7 : OSTaskStkChk_partial_solve_wit_7.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_8_pure : OSTaskStkChk_partial_solve_wit_8_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_8 : OSTaskStkChk_partial_solve_wit_8.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_9_pure : OSTaskStkChk_partial_solve_wit_9_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_9 : OSTaskStkChk_partial_solve_wit_9.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_10_pure : OSTaskStkChk_partial_solve_wit_10_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_10 : OSTaskStkChk_partial_solve_wit_10.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_11_pure : OSTaskStkChk_partial_solve_wit_11_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_11 : OSTaskStkChk_partial_solve_wit_11.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_12_pure : OSTaskStkChk_partial_solve_wit_12_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_12 : OSTaskStkChk_partial_solve_wit_12.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_13_pure : OSTaskStkChk_partial_solve_wit_13_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_13 : OSTaskStkChk_partial_solve_wit_13.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_14_pure : OSTaskStkChk_partial_solve_wit_14_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_14 : OSTaskStkChk_partial_solve_wit_14.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_15_pure : OSTaskStkChk_partial_solve_wit_15_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_15 : OSTaskStkChk_partial_solve_wit_15.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_16_pure : OSTaskStkChk_partial_solve_wit_16_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_16 : OSTaskStkChk_partial_solve_wit_16.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_17_pure : OSTaskStkChk_partial_solve_wit_17_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_17 : OSTaskStkChk_partial_solve_wit_17.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_18_pure : OSTaskStkChk_partial_solve_wit_18_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_18 : OSTaskStkChk_partial_solve_wit_18.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_19_pure : OSTaskStkChk_partial_solve_wit_19_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_19 : OSTaskStkChk_partial_solve_wit_19.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_20_pure : OSTaskStkChk_partial_solve_wit_20_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_20 : OSTaskStkChk_partial_solve_wit_20.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_21_pure : OSTaskStkChk_partial_solve_wit_21_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_21 : OSTaskStkChk_partial_solve_wit_21.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_22_pure : OSTaskStkChk_partial_solve_wit_22_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_22 : OSTaskStkChk_partial_solve_wit_22.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_23 : OSTaskStkChk_partial_solve_wit_23.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_24_pure : OSTaskStkChk_partial_solve_wit_24_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_24 : OSTaskStkChk_partial_solve_wit_24.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_25_pure : OSTaskStkChk_partial_solve_wit_25_pure.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_25 : OSTaskStkChk_partial_solve_wit_25.
Axiom proof_of_OSTaskStkChk_partial_solve_wit_26 : OSTaskStkChk_partial_solve_wit_26.
Axiom proof_of_OSTaskStkChk_which_implies_wit_1 : OSTaskStkChk_which_implies_wit_1.
Axiom proof_of_OSTaskStkChk_which_implies_wit_2 : OSTaskStkChk_which_implies_wit_2.
Axiom proof_of_OSTaskStkChk_which_implies_wit_3 : OSTaskStkChk_which_implies_wit_3.
Axiom proof_of_OSTaskStkChk_which_implies_wit_4 : OSTaskStkChk_which_implies_wit_4.
Axiom proof_of_OSTaskStkChk_which_implies_wit_5 : OSTaskStkChk_which_implies_wit_5.
Axiom proof_of_OSTaskStkChk_which_implies_wit_6 : OSTaskStkChk_which_implies_wit_6.
Axiom proof_of_OSTaskStkChk_which_implies_wit_7 : OSTaskStkChk_which_implies_wit_7.
Axiom proof_of_OSTaskStkChk_which_implies_wit_8 : OSTaskStkChk_which_implies_wit_8.
Axiom proof_of_OSTaskStkChk_which_implies_wit_9 : OSTaskStkChk_which_implies_wit_9.
Axiom proof_of_OSTaskStkChk_which_implies_wit_10 : OSTaskStkChk_which_implies_wit_10.
Axiom proof_of_OSTaskStkChk_which_implies_wit_11 : OSTaskStkChk_which_implies_wit_11.
Axiom proof_of_OSTaskStkChk_which_implies_wit_12 : OSTaskStkChk_which_implies_wit_12.
Axiom proof_of_OSTaskStkChk_which_implies_wit_13 : OSTaskStkChk_which_implies_wit_13.
Axiom proof_of_OSTaskStkChk_which_implies_wit_14 : OSTaskStkChk_which_implies_wit_14.
Axiom proof_of_OSTaskStkChk_which_implies_wit_15 : OSTaskStkChk_which_implies_wit_15.
Axiom proof_of_OSTaskStkChk_which_implies_wit_16 : OSTaskStkChk_which_implies_wit_16.
Axiom proof_of_OSTaskStkChk_which_implies_wit_17 : OSTaskStkChk_which_implies_wit_17.

End VC_Correct.
