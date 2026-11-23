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
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function App_TaskCreateHook -----*)

Definition App_TaskCreateHook_return_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

(*----- Function App_TCBInitHook -----*)

Definition App_TCBInitHook_return_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

(*----- Function OSTCBInitHook -----*)

Definition OSTCBInitHook_return_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

Definition OSTCBInitHook_partial_solve_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

(*----- Function OSTaskCreateHook -----*)

Definition OSTaskCreateHook_return_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

Definition OSTaskCreateHook_partial_solve_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

(*----- Function OS_TCBInit -----*)

Definition OS_TCBInit_safety_wit_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation initial acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_tcb_init_entry sg args invocation origin initial )) (PreH4 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH5 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired)))
  **  (task_tcb_init_public_without_free_root sg acquired )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired)))
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_3 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_4 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OS_TCBInit_safety_wit_4_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= prio_pre) ”
.

Definition OS_TCBInit_safety_wit_4_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (3 <= 31) ”
.

Definition OS_TCBInit_safety_wit_4_split_goal_3 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= 3) ”
.

Definition OS_TCBInit_safety_wit_5 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) <= 63) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8))) ”
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) <= 63) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8))) ”
).

Definition OS_TCBInit_safety_wit_5_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) <= 63) ”
.

Definition OS_TCBInit_safety_wit_5_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8))) ”
.

Definition OS_TCBInit_safety_wit_6 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OS_TCBInit_safety_wit_6_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OS_TCBInit_safety_wit_6_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OS_TCBInit_safety_wit_7 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_8 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_9 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_10 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_11 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) acquired_2 )) (PreH2 : (interrupt_saved_value (armv7a_irq_fiq_mask (cpu_sr)) retval )) (PreH3 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH4 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH5 : (critical_region_interval critical sg invocation initial acquired )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH8 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH9 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH10 : (i = 1)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (GlobalStrings LitMap )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_12 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired current slot )) (PreH17 : (UCOS2_state_inv sg current )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |->_)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  (task_tcb_init_used_storage sg current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_13 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired current slot )) (PreH17 : (UCOS2_state_inv sg current )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  (task_tcb_init_used_storage sg current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_14 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (i = 1)) (PreH5 : (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_15 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_tcb_init_result critical sg args invocation origin initial 66 acquired )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation acquired )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_entail_wit_1 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_tcb_init_entry sg args invocation origin initial )) (PreH4 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH5 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (GlobalStrings LitMap )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired)))
  **  (task_tcb_init_public_without_free_root sg acquired )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_tcb_init_entry sg args invocation origin initial )) (PreH4 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH5 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (GlobalStrings LitMap )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired)))
  **  (task_tcb_init_public_without_free_root sg acquired )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_2 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg) (acquired)) <> 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired)))
  **  (task_tcb_init_public_without_free_root sg acquired )
  **  (GlobalStrings LitMap )
|--
  EX (next_free: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired_2: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired_2 ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired_2 slot rest free_image ) ” 
  &&  “ (task_tcb_init_free_next_image free_image next_free ) ” 
  &&  “ (next_free = (task_tcb_init_free_next (sg) (rest))) ” 
  &&  “ ((task_tcb_init_free_root (sg) (acquired)) = (tcb64_addr (sg) (slot))) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired)))
  **  ((&(((task_tcb_init_free_root (sg) (acquired)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> next_free)
  **  (tcb64_storage_without (task_tcb_init_free_root (sg) (acquired)) TCBNext (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_public_without_free_head sg acquired_2 rest )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg) (acquired)) <> 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_tcb_init_public_without_free_root sg acquired )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired_2: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired_2 ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired_2 ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired_2 slot rest free_image ) ” 
  &&  “ (task_tcb_init_free_next_image free_image (task_tcb_init_free_next (sg) (rest)) ) ” 
  &&  “ ((task_tcb_init_free_root (sg) (acquired)) = (tcb64_addr (sg) (slot))) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((&(((task_tcb_init_free_root (sg) (acquired)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_free_next (sg) (rest)))
  **  (tcb64_storage_without (task_tcb_init_free_root (sg) (acquired)) TCBNext (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_public_without_free_head sg acquired_2 rest )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_3 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (next_free: Z) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (task_tcb_init_free_next_image free_image_2 next_free )) (PreH8 : (next_free = (task_tcb_init_free_next (sg) (rest_2)))) (PreH9 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> next_free)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> next_free)
  **  (tcb64_storage_without ptcb TCBNext (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_public_without_free_head sg acquired_2 rest_2 )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (next_free: Z) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (task_tcb_init_free_next_image free_image_2 next_free )) (PreH8 : (next_free = (task_tcb_init_free_next (sg) (rest_2)))) (PreH9 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> next_free)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> next_free)
  **  (tcb64_storage_without ptcb TCBNext (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_public_without_free_head sg acquired_2 rest_2 )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_4 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image_2)) )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |->_)
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image_2)) )
  **  (GlobalStrings LitMap )
|--
  EX (x_19: Z)  (x_18: Z)  (x_17: Z)  (x_16: Z)  (x_15: Z)  (x_14: Z)  (x_13: Z)  (x_12: Z)  (x_11: Z)  (x_10: Z)  (x_9: Z)  (x_8: Z)  (x_7: Z)  (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> x_19)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> x_18)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> x_17)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> x_16)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> x_15)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> x_14)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> x_13)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> x_12)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> x_11)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> x_10)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> x_9)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> x_8)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> x_7)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> x_6)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> x_5)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> x_4)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> x_3)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> x_2)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> x)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_5 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 0 (zeros (0)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 1 )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) = (prio_pre ÷ 8 )) ” 
  &&  “ ((Z.land prio_pre 7) = (prio_pre % ( 8 ) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)) = (Z.shiftl 1 (prio_pre ÷ 8 ))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (Z.shiftl 1 (prio_pre % ( 8 ) ))) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap (("?"%string)))) ” 
  &&  “ ((zeros (0)) = (@nil Z)) ”
  &&  emp
).

Definition OS_TCBInit_entail_wit_5_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) = (prio_pre ÷ 8 ))
.

Definition OS_TCBInit_entail_wit_5_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  ((Z.land prio_pre 7) = (prio_pre % ( 8 ) ))
.

Definition OS_TCBInit_entail_wit_5_split_goal_3 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)) = (Z.shiftl 1 (prio_pre ÷ 8 )))
.

Definition OS_TCBInit_entail_wit_5_split_goal_4 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (Z.shiftl 1 (prio_pre % ( 8 ) )))
.

Definition OS_TCBInit_entail_wit_5_split_goal_5 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap (("?"%string))))
.

Definition OS_TCBInit_entail_wit_5_split_goal_6 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) ,
  ((zeros (0)) = (@nil Z))
.

Definition OS_TCBInit_entail_wit_6 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (PreH1 : (i < 1)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 1)) ,
  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 (i + 1 ) (app ((zeros (i))) ((cons (0) ((@nil Z))))) )
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 1) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 (i + 1 ) (zeros ((i + 1 ))) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") (i + 1 ) 1 )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (PreH1 : (i < 1)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 1)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image_2)) )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ ((app ((zeros (i))) ((cons (0) ((@nil Z))))) = (zeros ((i + 1 )))) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 1) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") (i + 1 ) 1 )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_7 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (PreH1 : (i >= 1)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 1)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") i 1 )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (PreH1 : (stk_size_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (stk_size_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (i >= 1)) (PreH6 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH7 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH8 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH11 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH12 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH13 : (0 <= i)) (PreH14 : (i <= 1)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (GlobalStrings LitMap )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_8 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (acquired_3: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) acquired_3 )) (PreH2 : (interrupt_saved_value (armv7a_irq_fiq_mask (cpu_sr)) retval )) (PreH3 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH4 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH5 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH8 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH9 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH10 : (i = 1)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_3 )
  **  (UCOS2_raw_rep sg acquired_3 )
  **  (GlobalStrings LitMap )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image_2)))) )
|--
  EX (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |->_)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  (task_tcb_init_used_storage sg current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (acquired_3: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) acquired_3 )) (PreH2 : (interrupt_saved_value (armv7a_irq_fiq_mask (cpu_sr)) retval )) (PreH3 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH4 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH5 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH8 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH9 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH10 : (i = 1)) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_3 )
  **  (UCOS2_raw_rep sg acquired_3 )
  **  (GlobalStrings LitMap )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image_2)))) )
|--
  EX (x_2: Z)  (x: Z)  (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> x_2)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> x)
  **  (critical_region_masked platform critical sg invocation origin retval current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  (task_tcb_init_used_storage sg current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_9 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg) (current_2)) <> 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (i = 1)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= (prio_pre ÷ 8 ))) (PreH13 : ((prio_pre ÷ 8 ) < 8)) (PreH14 : (0 <= (prio_pre % ( 8 ) ))) (PreH15 : ((prio_pre % ( 8 ) ) < 8)) (PreH16 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH17 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH18 : (UCOS2_state_inv sg current_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  (task_tcb_init_used_storage sg current_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current_2)) )
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (previous: Z)  (head: Z)  (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (head = (task_tcb_init_active_head (sg) (current))) ” 
  &&  “ (head <> 0) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> head)
  **  ((&((head)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> previous)
  **  (task_tcb_init_used_without_head_prev sg current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg) (current_2)) <> 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (i = 1)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= (prio_pre ÷ 8 ))) (PreH13 : ((prio_pre ÷ 8 ) < 8)) (PreH14 : (0 <= (prio_pre % ( 8 ) ))) (PreH15 : ((prio_pre % ( 8 ) ) < 8)) (PreH16 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH17 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH18 : (UCOS2_state_inv sg current_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_used_storage sg current_2 )
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (previous: Z)  (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ ((task_tcb_init_priority_table (sg) (current_2)) = (task_tcb_init_priority_table (sg) (current))) ” 
  &&  “ ((task_tcb_init_ready_rows (current_2)) = (task_tcb_init_ready_rows (current))) ” 
  &&  “ ((task_tcb_init_ready_group (current_2)) = (task_tcb_init_ready_group (current))) ” 
  &&  “ ((task_tcb_init_count (current_2)) = (task_tcb_init_count (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg) (current_2)) = (task_tcb_init_active_head (sg) (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg) (current_2)) = (task_tcb_init_active_head (sg) (current))) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ ((task_tcb_init_active_head (sg) (current)) <> 0) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&(((task_tcb_init_active_head (sg) (current)))  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> previous)
  **  (task_tcb_init_used_without_head_prev sg current )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_10_1 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (head: Z) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH17 : (UCOS2_state_inv sg current_2 )) (PreH18 : (head = (task_tcb_init_active_head (sg) (current_2)))) (PreH19 : (head <> 0)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> head)
  **  ((&((head)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_without_head_prev sg current_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current_2)) )
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (head: Z) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH17 : (UCOS2_state_inv sg current_2 )) (PreH18 : (head = (task_tcb_init_active_head (sg) (current_2)))) (PreH19 : (head <> 0)) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((head)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_without_head_prev sg current_2 )
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ ((task_tcb_init_priority_table (sg) (current_2)) = (task_tcb_init_priority_table (sg) (current))) ” 
  &&  “ ((task_tcb_init_ready_rows (current_2)) = (task_tcb_init_ready_rows (current))) ” 
  &&  “ ((task_tcb_init_ready_group (current_2)) = (task_tcb_init_ready_group (current))) ” 
  &&  “ ((task_tcb_init_count (current_2)) = (task_tcb_init_count (current))) ” 
  &&  “ (head = (task_tcb_init_active_head (sg) (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg) (current_2)) = (task_tcb_init_active_head (sg) (current))) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_10_2 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg) (current_2)) = 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (i = 1)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= (prio_pre ÷ 8 ))) (PreH13 : ((prio_pre ÷ 8 ) < 8)) (PreH14 : (0 <= (prio_pre % ( 8 ) ))) (PreH15 : ((prio_pre % ( 8 ) ) < 8)) (PreH16 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH17 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH18 : (UCOS2_state_inv sg current_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  (task_tcb_init_used_storage sg current_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current_2)) )
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg) (current_2)) = 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest_2 free_image_2 )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH9 : (i = 1)) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= (prio_pre ÷ 8 ))) (PreH13 : ((prio_pre ÷ 8 ) < 8)) (PreH14 : (0 <= (prio_pre % ( 8 ) ))) (PreH15 : ((prio_pre % ( 8 ) ) < 8)) (PreH16 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH17 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH18 : (UCOS2_state_inv sg current_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_used_storage sg current_2 )
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (current: UCOS2_Verify_State)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State) ,
  “ ((task_tcb_init_priority_table (sg) (current_2)) = (task_tcb_init_priority_table (sg) (current))) ” 
  &&  “ ((task_tcb_init_ready_rows (current_2)) = (task_tcb_init_ready_rows (current))) ” 
  &&  “ ((task_tcb_init_ready_group (current_2)) = (task_tcb_init_ready_group (current))) ” 
  &&  “ ((task_tcb_init_count (current_2)) = (task_tcb_init_count (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg) (current_2)) = (task_tcb_init_active_head (sg) (current))) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_11 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest free_image_2 )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest) (free_image_2)) current_2 )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH17 : (UCOS2_state_inv sg current_2 )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb) ((task_tcb_init_priority_table (sg) (current_2)))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current_2)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current_2 slot_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current_2)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current_2))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (slot: Z)  (free_image: TCBLayoutImage) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (UCOS2_inv sg (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (stk_size_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (stk_size_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH6 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH7 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (task_tcb_init_entry sg args invocation origin acquired_2 )) (PreH10 : (task_tcb_init_detach_observation args invocation origin acquired_2 slot_2 rest free_image_2 )) (PreH11 : (ptcb = (tcb64_addr (sg) (slot_2)))) (PreH12 : (i = 1)) (PreH13 : (0 <= prio_pre)) (PreH14 : (prio_pre < 64)) (PreH15 : (0 <= (prio_pre ÷ 8 ))) (PreH16 : ((prio_pre ÷ 8 ) < 8)) (PreH17 : (0 <= (prio_pre % ( 8 ) ))) (PreH18 : ((prio_pre % ( 8 ) ) < 8)) (PreH19 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired_2) (slot_2) (rest) (free_image_2)) current_2 )) (PreH20 : (task_tcb_init_commit_binding args invocation origin acquired_2 current_2 slot_2 )) (PreH21 : (UCOS2_state_inv sg current_2 )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb) ((task_tcb_init_priority_table (sg) (current_2)))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current_2)))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current_2 )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current_2 slot_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current_2)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current_2))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (task_tcb_init_publication_other sg current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (slot: Z)  (free_image: TCBLayoutImage) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (UCOS2_inv sg (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_entail_wit_12 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg) (acquired_2)) = 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired_2)))
  **  (task_tcb_init_public_without_free_root sg acquired_2 )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired_2)))
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_result critical sg args invocation origin initial 66 acquired ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg) (acquired_2)) = 0)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired_2 )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2 )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg) (acquired_2)))
  **  (task_tcb_init_public_without_free_root sg acquired_2 )
  **  (GlobalStrings LitMap )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_result critical sg args invocation origin initial 66 acquired ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_return_wit_1 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_tcb_init_result critical sg args invocation origin initial 66 acquired )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation acquired )
  **  (GlobalStrings LitMap )
|--
  (task_tcb_init_post platform critical sg args invocation origin mask initial 66 )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_tcb_init_result critical sg args invocation origin initial 66 acquired )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation acquired )
  **  (GlobalStrings LitMap )
|--
  (task_tcb_init_post platform critical sg args invocation origin mask initial 66 )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_return_wit_1_split_goal_spatial := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_tcb_init_result critical sg args invocation origin initial 66 acquired )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation acquired )
  **  (GlobalStrings LitMap )
|--
  (task_tcb_init_post platform critical sg args invocation origin mask initial 66 )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_return_wit_2 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (i = 1)) (PreH5 : (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
|--
  (task_tcb_init_post platform critical sg args invocation origin mask initial 0 )
  **  (GlobalStrings LitMap )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (i = 1)) (PreH5 : (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
|--
  (task_tcb_init_post platform critical sg args invocation origin mask initial 0 )
  **  (GlobalStrings LitMap )
).

Definition OS_TCBInit_return_wit_2_split_goal_spatial := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (i = 1)) (PreH5 : (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
|--
  (task_tcb_init_post platform critical sg args invocation origin mask initial 0 )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) ,
  (task_tcb_init_pre platform critical sg args invocation origin mask initial )
  **  (GlobalStrings LitMap )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ”
  &&  (task_tcb_init_pre platform critical sg args invocation origin mask initial )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_tcb_init_entry sg args invocation origin initial )) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation initial )
  **  (GlobalStrings LitMap )
|--
  “ (task_tcb_init_entry sg args invocation origin initial ) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation initial )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_3_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings LitMap )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TCBInit_partial_solve_wit_3_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings LitMap )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_3 := OS_TCBInit_partial_solve_wit_3_pure -> OS_TCBInit_partial_solve_wit_3_aux.

Definition OS_TCBInit_partial_solve_wit_4 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (i: Z) (ptcb: Z) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (i < 1)) (PreH2 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH3 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH4 : (critical_region_interval critical sg invocation initial acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH7 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH8 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 1)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") i 1 )
  **  (GlobalStrings LitMap )
|--
  “ (i < 1) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 1) ”
  &&  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (i * sizeof(UINT)))) # UInt  |->_)
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_5 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) ,
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
  **  (GlobalStrings LitMap )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_6 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) ,
  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_7 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) ,
  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) )
  **  (GlobalStrings LitMap )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_8 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired current slot )) (PreH17 : (UCOS2_state_inv sg current )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((prio_pre ÷ 8 ) * sizeof(UCHAR)))) # UChar  |-> (Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current)) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (prio_pre ÷ 8 ) 0 8 (task_tcb_init_ready_rows (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_9 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired current slot )) (PreH17 : (UCOS2_state_inv sg current )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((prio_pre ÷ 8 ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (prio_pre ÷ 8 ) 0 8 (task_tcb_init_ready_rows (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_10 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (critical_region_interval critical sg invocation initial acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (task_tcb_init_entry sg args invocation origin acquired )) (PreH6 : (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image )) (PreH7 : (ptcb = (tcb64_addr (sg) (slot)))) (PreH8 : (i = 1)) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= (prio_pre ÷ 8 ))) (PreH12 : ((prio_pre ÷ 8 ) < 8)) (PreH13 : (0 <= (prio_pre % ( 8 ) ))) (PreH14 : ((prio_pre % ( 8 ) ) < 8)) (PreH15 : (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current )) (PreH16 : (task_tcb_init_commit_binding args invocation origin acquired current slot )) (PreH17 : (UCOS2_state_inv sg current )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current)))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
|--
  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (critical_region_interval critical sg invocation initial acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg args invocation origin acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args invocation origin acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (critical_region_interval critical sg invocation (task_tcb_init_detached_state (args) (invocation) (origin) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args invocation origin acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) prio_pre 0 64 (task_tcb_init_priority_table (sg) (current)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current)))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkPtr")) # Ptr  |-> ptos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBExtPtr")) # Ptr  |-> pext_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkSize")) # UInt  |-> stk_size_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStkBottom")) # Ptr  |-> pbos_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBOpt")) # UShort  |-> opt_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBId")) # UShort  |-> id_pre)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDelReq")) # UChar  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (prio_pre ÷ 8 ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (prio_pre % ( 8 ) ))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (Z.shiftl 1 (prio_pre ÷ 8 )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (Z.shiftl 1 (prio_pre % ( 8 ) )))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> 0)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (task_tcb_init_publication_other sg current )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_11_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (i = 1)) (PreH5 : (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (UCOS2_inv sg (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TCBInit_partial_solve_wit_11_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (i = 1)) (PreH5 : (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (UCOS2_inv sg (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_result critical sg args invocation origin initial 0 (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr current )
  **  (UCOS2_inv sg (task_tcb_init_published_state (sg) (args) (invocation) (acquired) (current) (slot) (free_image)) )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_11 := OS_TCBInit_partial_solve_wit_11_pure -> OS_TCBInit_partial_solve_wit_11_aux.

Definition OS_TCBInit_partial_solve_wit_12_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_tcb_init_result critical sg args invocation origin initial 66 acquired )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TCBInit_partial_solve_wit_12_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (task_tcb_init_result critical sg args invocation origin initial 66 acquired )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (GlobalStrings LitMap )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_global_addresses sg ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_tcb_init_result critical sg args invocation origin initial 66 acquired ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (GlobalStrings LitMap )
.

Definition OS_TCBInit_partial_solve_wit_12 := OS_TCBInit_partial_solve_wit_12_pure -> OS_TCBInit_partial_solve_wit_12_aux.

Definition OS_TCBInit_which_implies_wit_1 := 
(
forall (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_tcb_init_pre platform critical sg args invocation origin mask initial )
|--
  “ (task_tcb_init_entry sg args invocation origin initial ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation initial )
) \/
(
forall (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_tcb_init_pre platform critical sg args invocation origin mask initial )
|--
  “ (task_tcb_init_entry sg args invocation origin initial ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation initial )
).

Definition OS_TCBInit_which_implies_wit_1_split_goal_1 := 
forall (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_tcb_init_pre platform critical sg args invocation origin mask initial )
|--
  “ (task_tcb_init_entry sg args invocation origin initial ) ”
.

Definition OS_TCBInit_which_implies_wit_1_split_goal_spatial := 
forall (initial: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (args: TaskTCBInitArgs) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_tcb_init_pre platform critical sg args invocation origin mask initial )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation initial )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_App_TaskCreateHook_return_wit_1 : App_TaskCreateHook_return_wit_1.
Axiom proof_of_App_TCBInitHook_return_wit_1 : App_TCBInitHook_return_wit_1.
Axiom proof_of_OSTCBInitHook_return_wit_1 : OSTCBInitHook_return_wit_1.
Axiom proof_of_OSTCBInitHook_partial_solve_wit_1 : OSTCBInitHook_partial_solve_wit_1.
Axiom proof_of_OSTaskCreateHook_return_wit_1 : OSTaskCreateHook_return_wit_1.
Axiom proof_of_OSTaskCreateHook_partial_solve_wit_1 : OSTaskCreateHook_partial_solve_wit_1.
Axiom proof_of_OS_TCBInit_safety_wit_1 : OS_TCBInit_safety_wit_1.
Axiom proof_of_OS_TCBInit_safety_wit_2 : OS_TCBInit_safety_wit_2.
Axiom proof_of_OS_TCBInit_safety_wit_3 : OS_TCBInit_safety_wit_3.
Axiom proof_of_OS_TCBInit_safety_wit_4 : OS_TCBInit_safety_wit_4.
Axiom proof_of_OS_TCBInit_safety_wit_5 : OS_TCBInit_safety_wit_5.
Axiom proof_of_OS_TCBInit_safety_wit_6 : OS_TCBInit_safety_wit_6.
Axiom proof_of_OS_TCBInit_safety_wit_7 : OS_TCBInit_safety_wit_7.
Axiom proof_of_OS_TCBInit_safety_wit_8 : OS_TCBInit_safety_wit_8.
Axiom proof_of_OS_TCBInit_safety_wit_9 : OS_TCBInit_safety_wit_9.
Axiom proof_of_OS_TCBInit_safety_wit_10 : OS_TCBInit_safety_wit_10.
Axiom proof_of_OS_TCBInit_safety_wit_11 : OS_TCBInit_safety_wit_11.
Axiom proof_of_OS_TCBInit_safety_wit_12 : OS_TCBInit_safety_wit_12.
Axiom proof_of_OS_TCBInit_safety_wit_13 : OS_TCBInit_safety_wit_13.
Axiom proof_of_OS_TCBInit_safety_wit_14 : OS_TCBInit_safety_wit_14.
Axiom proof_of_OS_TCBInit_safety_wit_15 : OS_TCBInit_safety_wit_15.
Axiom proof_of_OS_TCBInit_entail_wit_1 : OS_TCBInit_entail_wit_1.
Axiom proof_of_OS_TCBInit_entail_wit_2 : OS_TCBInit_entail_wit_2.
Axiom proof_of_OS_TCBInit_entail_wit_3 : OS_TCBInit_entail_wit_3.
Axiom proof_of_OS_TCBInit_entail_wit_4 : OS_TCBInit_entail_wit_4.
Axiom proof_of_OS_TCBInit_entail_wit_5 : OS_TCBInit_entail_wit_5.
Axiom proof_of_OS_TCBInit_entail_wit_6 : OS_TCBInit_entail_wit_6.
Axiom proof_of_OS_TCBInit_entail_wit_7 : OS_TCBInit_entail_wit_7.
Axiom proof_of_OS_TCBInit_entail_wit_8 : OS_TCBInit_entail_wit_8.
Axiom proof_of_OS_TCBInit_entail_wit_9 : OS_TCBInit_entail_wit_9.
Axiom proof_of_OS_TCBInit_entail_wit_10_1 : OS_TCBInit_entail_wit_10_1.
Axiom proof_of_OS_TCBInit_entail_wit_10_2 : OS_TCBInit_entail_wit_10_2.
Axiom proof_of_OS_TCBInit_entail_wit_11 : OS_TCBInit_entail_wit_11.
Axiom proof_of_OS_TCBInit_entail_wit_12 : OS_TCBInit_entail_wit_12.
Axiom proof_of_OS_TCBInit_return_wit_1 : OS_TCBInit_return_wit_1.
Axiom proof_of_OS_TCBInit_return_wit_2 : OS_TCBInit_return_wit_2.
Axiom proof_of_OS_TCBInit_partial_solve_wit_1 : OS_TCBInit_partial_solve_wit_1.
Axiom proof_of_OS_TCBInit_partial_solve_wit_2 : OS_TCBInit_partial_solve_wit_2.
Axiom proof_of_OS_TCBInit_partial_solve_wit_3_pure : OS_TCBInit_partial_solve_wit_3_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_3 : OS_TCBInit_partial_solve_wit_3.
Axiom proof_of_OS_TCBInit_partial_solve_wit_4 : OS_TCBInit_partial_solve_wit_4.
Axiom proof_of_OS_TCBInit_partial_solve_wit_5 : OS_TCBInit_partial_solve_wit_5.
Axiom proof_of_OS_TCBInit_partial_solve_wit_6 : OS_TCBInit_partial_solve_wit_6.
Axiom proof_of_OS_TCBInit_partial_solve_wit_7 : OS_TCBInit_partial_solve_wit_7.
Axiom proof_of_OS_TCBInit_partial_solve_wit_8 : OS_TCBInit_partial_solve_wit_8.
Axiom proof_of_OS_TCBInit_partial_solve_wit_9 : OS_TCBInit_partial_solve_wit_9.
Axiom proof_of_OS_TCBInit_partial_solve_wit_10 : OS_TCBInit_partial_solve_wit_10.
Axiom proof_of_OS_TCBInit_partial_solve_wit_11_pure : OS_TCBInit_partial_solve_wit_11_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_11 : OS_TCBInit_partial_solve_wit_11.
Axiom proof_of_OS_TCBInit_partial_solve_wit_12_pure : OS_TCBInit_partial_solve_wit_12_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_12 : OS_TCBInit_partial_solve_wit_12.
Axiom proof_of_OS_TCBInit_which_implies_wit_1 : OS_TCBInit_which_implies_wit_1.

End VC_Correct.
